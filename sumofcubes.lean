import Mathlib.Tactic

/- Main goal: prove that $∑ _{i=0}^n (i^3) = (∑ _{i=0}^n (i))^2$ -/
/- We first prove that $∑_{i=0}^n i = n(n+1)/2$, which gives a formula that is easier to use -/

def S
| 0 => 0
| n + 1 => S n + (n+1)

def C
| 0 => 0
| n + 1 => C n + (n+1)^3

lemma prod_succ_even (n : ℕ) : Even (n*(n+1)) := by
  dsimp [Even]
  ring

  -- Structure from Lean docs
  cases Nat.even_or_odd n with
  | inl h_even =>
    obtain ⟨k, hk⟩ := h_even
    use k*(2*k+1)
    rw [hk]
    ring
  | inr h_odd =>
    obtain ⟨k, hk⟩ := h_odd
    use (2*k+1)*(k+1)
    rw[hk]
    ring

theorem sqsum (n : ℕ) : S n = n*(n+1) / 2 := by
  -- Initiate induction (I know that this is different from Macbeth, but just thought it
  -- would be a good chance to get used to more standard Lean)
  induction n with
  | zero =>
    rw[S]
  | succ n ih =>
    have h_gauss_times_2: 2*(S (n+1)) = (n+1)*(n+1+1) := by
      have h_prod_even := prod_succ_even n
      obtain ⟨r, hr⟩ := h_prod_even
      have h_2_div_r_plus_r :  2 ∣ (r+r) := by
        use r
        ring
      calc
        2 * S (n + 1) = 2 * (S n + (n + 1)) := by rw [S]
        _ = 2 * S n + 2 * (n + 1) := by ring
        _ = 2 * ((r + r) / 2) + 2 * (n + 1) := by rw [ih, hr]
         -- mul_div_cancel'-- allows the twos to be cancelled, but we must prove divisibility
        _ = (r+r) + 2*(n+1) := by rw[Nat.mul_div_cancel' (h_2_div_r_plus_r)]
        _ = n*(n+1) + 2*(n+1) := by rw[hr]
        _ = (n+1)*(n+2) := by ring
    have : Even (S (n+1)*2 : ℕ) := by
      have : S (n+1) * 2 = 2 * S (n+1) := by ring
      rw[this]
      rw[h_gauss_times_2]
      apply prod_succ_even
    obtain ⟨r, hr⟩ := this
    calc
    -- norm_num needed since must prove 0 < 2
      S (n+1) = (S (n+1)*2) / 2 := by norm_num
      _ = (2*S (n+1)) / 2 := by ring
      _ = (n+1)*(n+2) / 2 := by rw[h_gauss_times_2]

theorem cbsum (n : ℕ) : C n = (S n)^2 := by
  -- Induction again :)
  induction n with
  | zero =>
    rw[C, S]
    norm_num
  | succ n ih =>
    have h_2_div_r_plus_r: 2 ∣ n*(n+1) := by
      obtain ⟨r, hr⟩ := prod_succ_even n
      use r
      rw[hr]
      ring
    calc
      C (n+1) = C n + (n+1)^3 := by rw[C]
      _ = (S n)^2 + (n+1)^3 := by rw[ih]
      _ = (n*(n+1)/2)^2 + (n+1)^3 := by rw[sqsum n]
      _ = (n*(n+1)/2)^2 + ((n+1)^3*4)/4 := by rw[Nat.mul_div_cancel]; norm_num
      _ = (n*(n+1))^2 / 4 + ((n+1)^3*4) / 4 := by rw[Nat.div_pow (h_2_div_r_plus_r)];
      _ = ((n*(n+1))^2 + ((n+1)^3*4)) / 4 := by
        -- Over integers, a / c + b / c ≠ (a+b) / c in general; there is an added term (see def.)
        -- Our goal is to prove that the added term is zero, which we do by proving that n*(n+1)
        -- is divided evenly by 4 and that 0 < 4.
        rw[Nat.add_div]
        · norm_num
          obtain ⟨r, hr⟩ := prod_succ_even n
          rw[hr]
          ring
          norm_num
        · norm_num
      _ = ((n+1)*(n+2))^2 / 4 := by ring
      _ = ((n+1)*(n+2) / 2)^2 := by
        rw[Nat.div_pow]
        · obtain ⟨r, hr⟩ := prod_succ_even (n+1)
          use r
          simp[hr]
          ring
      _ = (S (n+1))^2 := by rw[sqsum (n+1)]

theorem cbsum_formula (n : ℕ) : C n = n^2*(n+1)^2/4 := by
  rw[cbsum]
  · rw[sqsum n]
    rw[Nat.div_pow]
    · ring_nf
    -- Must now prove that 2 ∣ n*(n+1)
    obtain ⟨r, hr⟩ := prod_succ_even n
    use r
    rw[hr]
    ring
