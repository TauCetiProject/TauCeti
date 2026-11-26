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
(`TauCeti.exists_orthonormalBasis_fin_apply_zero_eq`).
-/

public section

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
  classical
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
  let v : Fin (k + l) → W := Fin.append a 0
  have hv : Orthonormal 𝕜 ((Set.range (Fin.castAdd l)).domRestrict v) := by
    rw [orthonormal_iff_ite]
    rintro ⟨_, i, rfl⟩ ⟨_, j, rfl⟩
    simp [v, Set.domRestrict, Subtype.ext_iff, orthonormal_iff_ite.1 ha i j]
  obtain ⟨c, hc⟩ := hv.exists_orthonormalBasis_extension_of_card_eq (by simp [hW])
  refine ⟨c, fun i ↦ ?_⟩
  have hci : c (Fin.castAdd l i) = a i := (hc _ (Set.mem_range_self i)).trans (Fin.append_left ..)
  rw [hci, ← LinearMap.domRestrict_apply]
  exact LinearMap.mem_ker.1 (B (Fin.castLE hK i)).property

end Orthonormal

namespace TauCeti

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- In a space of dimension `n + 1`, every unit vector `e` is the first vector of an orthonormal
basis indexed by `Fin (n + 1)`. -/
theorem exists_orthonormalBasis_fin_apply_zero_eq {n : ℕ} (hn : Module.finrank 𝕜 E = n + 1)
    {e : E} (he : ‖e‖ = 1) : ∃ b : OrthonormalBasis (Fin (n + 1)) 𝕜 E, b 0 = e := by
  have : FiniteDimensional 𝕜 E := Module.finite_of_finrank_eq_succ hn
  obtain ⟨b, hb⟩ := Orthonormal.exists_orthonormalBasis_extension_of_card_eq (𝕜 := 𝕜)
    (ι := Fin (n + 1)) (by simp [hn]) (v := fun _ ↦ e) (s := {0}) <| by
      rw [orthonormal_iff_ite]
      rintro ⟨i, hi⟩ ⟨j, hj⟩
      simp only [Set.mem_singleton_iff] at hi hj
      subst hi hj
      simp [he]
  exact ⟨b, hb 0 rfl⟩

end TauCeti
