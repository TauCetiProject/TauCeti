/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
import TauCeti.Analysis.InnerProductSpace.Projection.Basic

/-!
# Extending orthonormal frames

In an inner product space of dimension at least four, every orthonormal pair extends to an
orthonormal four-frame (`Orthonormal.exists_fin_four_extension`). The span of an orthonormal
`(k + l)`-frame has an orthonormal basis whose first `k` vectors lie in the kernel of a given
linear map into a space of dimension at most `l`
(`Orthonormal.exists_orthonormalBasis_span_apply_castAdd_eq_zero`). In a space of dimension
`n + 1`, every unit vector is the first vector of an orthonormal basis indexed by `Fin (n + 1)`
(`TauCeti.exists_orthonormalBasis_fin_apply_zero_eq`), and more generally every orthonormal
`k`-frame consists of the first `k` vectors of an orthonormal basis indexed by `Fin n`
(`TauCeti.exists_orthonormalBasis_fin_apply_castLE_eq`). In the same way an orthonormal `k`-frame
in the span of an orthonormal `n`-frame `v` consists of the first `k` vectors of an orthonormal
`n`-frame with the span of `v` (`Orthonormal.exists_orthonormal_span_eq_apply_castLE_eq`).
-/

public section

namespace TauCeti

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- In a finite-dimensional space of dimension `n`, every orthonormal family `e` of `k` vectors
consists of the first `k` vectors of an orthonormal basis indexed by `Fin n`. -/
theorem exists_orthonormalBasis_fin_apply_castLE_eq [FiniteDimensional 𝕜 E] {k n : ℕ}
    (hn : Module.finrank 𝕜 E = n) (hkn : k ≤ n) {e : Fin k → E} (he : Orthonormal 𝕜 e) :
    ∃ b : OrthonormalBasis (Fin n) 𝕜 E, ∀ i, b (Fin.castLE hkn i) = e i := by
  classical
  let v : Fin n → E := fun j ↦ if h : (j : ℕ) < k then e ⟨j, h⟩ else 0
  have hv : Orthonormal 𝕜 ((Set.range (Fin.castLE hkn)).domRestrict v) := by
    rw [orthonormal_iff_ite]
    rintro ⟨_, i, rfl⟩ ⟨_, j, rfl⟩
    simp [v, Set.domRestrict, Subtype.ext_iff, orthonormal_iff_ite.1 he i j, Fin.ext_iff]
  obtain ⟨b, hb⟩ := hv.exists_orthonormalBasis_extension_of_card_eq (by simp [hn])
  exact ⟨b, fun i ↦ (hb _ (Set.mem_range_self i)).trans (by simp [v])⟩

/-- In a space of dimension `n + 1`, every unit vector `e` is the first vector of an orthonormal
basis indexed by `Fin (n + 1)`. -/
theorem exists_orthonormalBasis_fin_apply_zero_eq {n : ℕ} (hn : Module.finrank 𝕜 E = n + 1)
    {e : E} (he : ‖e‖ = 1) : ∃ b : OrthonormalBasis (Fin (n + 1)) 𝕜 E, b 0 = e := by
  have : FiniteDimensional 𝕜 E := Module.finite_of_finrank_eq_succ hn
  obtain ⟨b, hb⟩ := exists_orthonormalBasis_fin_apply_castLE_eq hn (Nat.le_add_left 1 n)
    (e := fun _ : Fin 1 ↦ e) ⟨fun _ ↦ he, fun i j hij ↦ (hij (Subsingleton.elim i j)).elim⟩
  exact ⟨b, by simpa using hb 0⟩

end TauCeti

namespace Orthonormal

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- In dimension at least four, every orthonormal pair `![u, v]` extends to an orthonormal
four-frame `f` with `f 0 = u` and `f 2 = v`. -/
theorem exists_fin_four_extension {u v : E} (huv : Orthonormal 𝕜 ![u, v])
    (hn : 4 ≤ Module.finrank 𝕜 E) :
    ∃ f : Fin 4 → E, Orthonormal 𝕜 f ∧ f 0 = u ∧ f 2 = v := by
  classical
  obtain ⟨w₁, hw₁, hw₁o⟩ := TauCeti.exists_norm_eq_one_forall_inner_eq_zero_of_card_lt_finrank
    (𝕜 := 𝕜) ({u, v} : Finset E) (Finset.card_le_two.trans_lt (by omega))
  obtain ⟨w₂, hw₂, hw₂o⟩ := TauCeti.exists_norm_eq_one_forall_inner_eq_zero_of_card_lt_finrank
    (𝕜 := 𝕜) ({u, v, w₁} : Finset E) (Finset.card_le_three.trans_lt (by omega))
  have hu : ‖u‖ = 1 := huv.1 0; have hv : ‖v‖ = 1 := huv.1 1
  have huv0 : inner 𝕜 u v = 0 := huv.2 (by decide : (0 : Fin 2) ≠ 1)
  refine ⟨![u, w₁, v, w₂], ?_, rfl, rfl⟩
  simp [Fin.forall_fin_succ, hu, hv, huv0, hw₁, hw₂, hw₁o u (by simp),
    inner_eq_zero_symm.2 (hw₁o v (by simp)), hw₂o u (by simp), hw₂o v (by simp), hw₂o w₁ (by simp)]

/-- The span of an orthonormal `(k + l)`-frame `u` has an orthonormal basis whose first `k`
vectors lie in the kernel of a linear map `q` into a space of dimension at most `l`. -/
theorem exists_orthonormalBasis_span_apply_castAdd_eq_zero {k l : ℕ} {u : Fin (k + l) → E}
    (hu : Orthonormal 𝕜 u) {G : Type*} [AddCommGroup G] [Module 𝕜 G] [FiniteDimensional 𝕜 G]
    (q : E →ₗ[𝕜] G) (hq : Module.finrank 𝕜 G ≤ l) :
    ∃ c : OrthonormalBasis (Fin (k + l)) 𝕜 (Submodule.span 𝕜 (Set.range u)),
      ∀ i, q (c (Fin.castAdd l i)) = 0 := by
  -- The kernel of `q` on the span has dimension at least `k`; an orthonormal `k`-frame in it is
  -- extended to an orthonormal basis of the span.
  let W := Submodule.span 𝕜 (Set.range u)
  have : FiniteDimensional 𝕜 W := FiniteDimensional.span_of_finite 𝕜 (Set.finite_range u)
  have hW : Module.finrank 𝕜 W = k + l := by
    simpa using finrank_span_eq_card hu.linearIndependent
  let L : W →ₗ[𝕜] G := q.domRestrict W
  have hK : k ≤ Module.finrank 𝕜 (LinearMap.ker L) := by
    have h₁ := L.finrank_range_add_finrank_ker
    have h₂ := (Submodule.finrank_le (LinearMap.range L)).trans hq
    omega
  let B := stdOrthonormalBasis 𝕜 (LinearMap.ker L)
  let a : Fin k → W := fun i ↦ B (Fin.castLE hK i)
  have ha : Orthonormal 𝕜 a :=
    (B.orthonormal.comp _ (Fin.castLE_injective hK)).comp_linearIsometry
      (LinearMap.ker L).subtypeₗᵢ
  obtain ⟨c, hc⟩ := TauCeti.exists_orthonormalBasis_fin_apply_castLE_eq hW
    (Nat.le_add_right k l) ha
  refine ⟨c, fun i ↦ ?_⟩
  rw [Fin.castAdd, hc, ← LinearMap.domRestrict_apply]
  exact LinearMap.mem_ker.1 (B (Fin.castLE hK i)).property

/-- An orthonormal family `e` of `k` vectors in the span of an orthonormal family `v` of `n ≥ k`
vectors consists of the first `k` vectors of an orthonormal family of `n` vectors with the same
span as `v`. -/
theorem exists_orthonormal_span_eq_apply_castLE_eq {n : ℕ} {v : Fin n → E} (hv : Orthonormal 𝕜 v)
    {k : ℕ} (hkn : k ≤ n) {e : Fin k → E} (he : Orthonormal 𝕜 e)
    (hev : ∀ i, e i ∈ Submodule.span 𝕜 (Set.range v)) :
    ∃ w : Fin n → E, Orthonormal 𝕜 w ∧
      Submodule.span 𝕜 (Set.range w) = Submodule.span 𝕜 (Set.range v) ∧
      ∀ i, w (Fin.castLE hkn i) = e i := by
  set W := Submodule.span 𝕜 (Set.range v)
  have : FiniteDimensional 𝕜 W := FiniteDimensional.span_of_finite 𝕜 (Set.finite_range v)
  have hW : Module.finrank 𝕜 W = n := by simpa using finrank_span_eq_card hv.linearIndependent
  obtain ⟨b, hb⟩ := TauCeti.exists_orthonormalBasis_fin_apply_castLE_eq hW hkn
    (e := fun i ↦ ⟨e i, hev i⟩) (W.subtypeₗᵢ.orthonormal_comp_iff.1 he)
  refine ⟨W.subtype ∘ b, ?_, ?_, fun i ↦ by simp [hb]⟩
  · simpa only [Submodule.coe_subtypeₗᵢ] using b.orthonormal.comp_linearIsometry W.subtypeₗᵢ
  · rw [Set.range_comp, ← b.coe_toBasis, ← Submodule.map_span, b.toBasis.span_eq,
      Submodule.map_top, W.range_subtype]

end Orthonormal
