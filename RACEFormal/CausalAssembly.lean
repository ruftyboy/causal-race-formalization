import RACEFormal.Deterministic

open scoped BigOperators

namespace RACEFormal

/--
If every approximate score differs from its target by at most `eps`, then the
normalized attention-output error is controlled by the prefix length times `eps`.
This is the deterministic assembly step used after the causal-triangle concentration event.
-/
theorem entrywise_error_to_output_bound
    {m : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (a b : Fin m → ℝ) (V : Fin m → E) (D eps : ℝ)
    (ha : ∀ j, 0 ≤ a j) (hb : ∀ j, 0 ≤ b j)
    (hA : 0 < ∑ j, a j) (hB : 0 < ∑ j, b j)
    (hD : 0 ≤ D) (_heps : 0 ≤ eps)
    (hdiam : ∀ j k, ‖V j - V k‖ ≤ D)
    (hentry : ∀ j, |a j - b j| ≤ eps) :
    ‖∑ j, (b j / (∑ i, b i) - a j / (∑ i, a i)) • V j‖
      ≤ D * min 1 (((m : ℝ) * eps) / (∑ i, a i)) := by
  have heta : (∑ j, |a j - b j|) ≤ (m : ℝ) * eps := by
    calc
      (∑ j, |a j - b j|) ≤ ∑ _j : Fin m, eps := by
        exact Finset.sum_le_sum fun j hj => hentry j
      _ = (m : ℝ) * eps := by simp
  have hratio :
      (∑ j, |a j - b j|) / (∑ i, a i)
        ≤ ((m : ℝ) * eps) / (∑ i, a i) := by
    exact (div_le_div_iff_of_pos_right hA).2 heta
  have hmin :
      min 1 ((∑ j, |a j - b j|) / (∑ i, a i))
        ≤ min 1 (((m : ℝ) * eps) / (∑ i, a i)) := by
    exact min_le_min (le_refl 1) hratio
  calc
    ‖∑ j, (b j / (∑ i, b i) - a j / (∑ i, a i)) • V j‖
        ≤ D * min 1 ((∑ j, |a j - b j|) / (∑ i, a i)) :=
          diameter_sensitive_normalization_stability a b V D ha hb hA hB hD hdiam
    _ ≤ D * min 1 (((m : ℝ) * eps) / (∑ i, a i)) :=
      mul_le_mul_of_nonneg_left hmin hD

/--
Bias and variance can be combined entrywise before normalization.  This formally
checks the deterministic implication used in the original causal RACE theorem:
`|b-mu| ≤ u` and `|mu-a| ≤ B` imply a final score error at most `u+B`.
-/
theorem bias_variance_to_output_bound
    {m : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (a mu b : Fin m → ℝ) (V : Fin m → E) (D u B : ℝ)
    (ha : ∀ j, 0 ≤ a j) (hb : ∀ j, 0 ≤ b j)
    (hA : 0 < ∑ j, a j) (hB : 0 < ∑ j, b j)
    (hD : 0 ≤ D) (hu : 0 ≤ u) (hBias : 0 ≤ B)
    (hdiam : ∀ j k, ‖V j - V k‖ ≤ D)
    (hvariance : ∀ j, |b j - mu j| ≤ u)
    (hbias : ∀ j, |mu j - a j| ≤ B) :
    ‖∑ j, (b j / (∑ i, b i) - a j / (∑ i, a i)) • V j‖
      ≤ D * min 1 (((m : ℝ) * (u + B)) / (∑ i, a i)) := by
  have hentry : ∀ j, |a j - b j| ≤ u + B := by
    intro j
    calc
      |a j - b j| = |(a j - mu j) + (mu j - b j)| := by ring_nf
      _ ≤ |a j - mu j| + |mu j - b j| := abs_add_le _ _
      _ ≤ B + u := by
        exact add_le_add (by simpa [abs_sub_comm] using hbias j)
          (by simpa [abs_sub_comm] using hvariance j)
      _ = u + B := by ring
  exact entrywise_error_to_output_bound a b V D (u + B) ha hb hA hB hD
    (add_nonneg hu hBias) hdiam hentry

end RACEFormal
