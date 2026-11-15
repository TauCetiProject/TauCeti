/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
public import Mathlib.LinearAlgebra.Quotient.Bilinear
import TauCeti.LinearAlgebra.BilinearForm.Orthogonal

/-!
# Symplectic normal spaces of forms with values in a module

Let `B : V → V → Q` be a reflexive bilinear map with values in a module `Q`, and let `W` be a
subspace of `V`. Its orthogonal `W^⊥ = {v | ∀ w ∈ W, B w v = 0}` is `Submodule.orthogonalBilin`.
The **symplectic normal space** of `W` is the quotient `W^⊥ ⧸ (W ∩ W^⊥)`
(`LinearMap.SymplecticNormal B W`). Since `B` is reflexive, it descends to a `Q`-valued form on
this quotient, `[u], [v] ↦ B u v` (`LinearMap.IsRefl.symplecticNormalForm`), alternating when `B`
is. For an isotropic subspace, `W ≤ W^⊥`, this is the quotient `W^⊥ ⧸ W`.

The main case is that of a line: `Q` is one-dimensional and `B` is nondegenerate, in the sense
that `v ↦ B v` is injective. This is the shape of the Levi form `ξ × ξ → TM ⧸ ξ` of a contact
structure, whose values lie in the contact line rather than in the scalars. Then:

* the induced form on the symplectic normal space is again nondegenerate
  (`LinearMap.IsRefl.injective_symplecticNormalForm`), and identifying `Q` with the scalars by any
  nonzero functional makes it a nondegenerate bilinear form
  (`LinearMap.IsRefl.nondegenerate_compr₂_symplecticNormalForm`);
* for an isotropic `W`, `dim (W^⊥ ⧸ W) + 2 dim W = dim V`
  (`LinearMap.finrank_symplecticNormal_add_two_mul_finrank`), so the symplectic normal space is
  zero exactly when `W` has half the dimension of `V`
  (`LinearMap.subsingleton_symplecticNormal_iff`).

For a scalar-valued symplectic form `ω` the same quotient appears in linear reduction as the
reduced space `TauCeti.SymplecticForm.ReducedSpace ω (ω.orthogonal W)`, written there as the
quotient of `W^ω` by the kernel of the restricted form. The module-valued version is the one
needed for the conformal symplectic normal spaces of isotropic submanifolds of contact manifolds,
whose Levi form takes values in the contact line: a contact structure need not have a global
defining form.

## References

* H. Geiges, *An Introduction to Contact Topology*, Cambridge Studies in Advanced Mathematics 109
  (2008), Section 2.5 (the conformal symplectic normal bundle of an isotropic submanifold).
* A. Weinstein, *Neighborhood classification of isotropic embeddings*, Journal of Differential
  Geometry 16 (1981), 125–128 (the symplectic normal bundle `TN^ω ⧸ TN` of an isotropic
  submanifold).
-/

public section

noncomputable section

open Module

namespace LinearMap

section CommRing

variable {K V Q : Type*} [CommRing K] [AddCommGroup V] [Module K V] [AddCommGroup Q] [Module K Q]
  {B : V →ₗ[K] V →ₗ[K] Q} {W : Submodule K V}

variable (B W) in
/-- The **symplectic normal space** `W^⊥ ⧸ (W ∩ W^⊥)` of a subspace `W` for a bilinear map `B`,
where `W^⊥ = {v | ∀ w ∈ W, B w v = 0}` is the orthogonal `Submodule.orthogonalBilin`. For an
isotropic `W` this is `W^⊥ ⧸ W`. -/
abbrev SymplecticNormal : Type _ :=
  W.orthogonalBilin B ⧸ W.comap (W.orthogonalBilin B).subtype

/-- The intersection of `W` with its orthogonal pairs to zero with the whole orthogonal: this is
what lets a reflexive form descend to the symplectic normal space. -/
private theorem comap_le_ker_domRestrict₁₂ :
    W.comap (W.orthogonalBilin B).subtype ≤
      LinearMap.ker (B.domRestrict₁₂ (W.orthogonalBilin B) (W.orthogonalBilin B)) :=
  fun w hw ↦ LinearMap.mem_ker.2 <| LinearMap.ext fun u ↦ u.2 w hw

variable (W) in
/-- The form `[u], [v] ↦ B u v` induced by a reflexive bilinear map `B` on the symplectic normal
space `W^⊥ ⧸ (W ∩ W^⊥)` of a subspace `W`. -/
def IsRefl.symplecticNormalForm (hB : B.IsRefl) :
    SymplecticNormal B W →ₗ[K] SymplecticNormal B W →ₗ[K] Q :=
  IsRefl.liftQ₂ (B.domRestrict₁₂ _ _) _ (hB.domRestrict _) comap_le_ker_domRestrict₁₂

/-- The defining formula `[u], [v] ↦ B u v` of the form on the symplectic normal space. -/
@[simp]
theorem IsRefl.symplecticNormalForm_mk (hB : B.IsRefl) (u v : W.orthogonalBilin B) :
    hB.symplecticNormalForm W (Submodule.Quotient.mk u) (Submodule.Quotient.mk v) = B u v :=
  (rfl)

/-- The form induced on the symplectic normal space by a reflexive form is reflexive. -/
theorem IsRefl.isRefl_symplecticNormalForm (hB : B.IsRefl) :
    (hB.symplecticNormalForm W).IsRefl := by
  intro x y
  induction x using Submodule.Quotient.induction_on with
  | H u =>
    induction y using Submodule.Quotient.induction_on with
    | H v => exact hB u v

/-- The form induced on the symplectic normal space by an alternating form is alternating. -/
theorem IsAlt.isAlt_symplecticNormalForm (hB : B.IsAlt) :
    (hB.isRefl.symplecticNormalForm W).IsAlt := by
  intro x
  induction x using Submodule.Quotient.induction_on with
  | H u => simpa using hB u

end CommRing

section Field

variable {K V Q : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  [AddCommGroup Q] [Module K Q] {B : V →ₗ[K] V →ₗ[K] Q} {W : Submodule K V}

/-- **The induced form on the symplectic normal space is nondegenerate.** If the reflexive
bilinear map `B : V → Hom(V, Q)` is injective and `Q` is one-dimensional, then so is the induced
map on the symplectic normal space of any subspace `W`. -/
theorem IsRefl.injective_symplecticNormalForm (hB : B.IsRefl) (hinj : Function.Injective B)
    (hQ : finrank K Q = 1) : Function.Injective (hB.symplecticNormalForm W) := by
  refine (injective_iff_map_eq_zero _).2 fun x hx ↦ ?_
  induction x using Submodule.Quotient.induction_on with
  | H u =>
    -- `u` pairs to zero with `W^⊥`, so it lies in `W^⊥⊥ = W`.
    have hu : (u : V) ∈ (W.orthogonalBilin B).orthogonalBilin B := fun v hv ↦ by
      have := LinearMap.congr_fun hx (Submodule.Quotient.mk ⟨v, hv⟩)
      simp only [symplecticNormalForm_mk] at this
      exact hB _ _ this
    rw [hB.orthogonalBilin_orthogonalBilin_of_injective hinj hQ W] at hu
    simpa using hu

/-- **Identifying the line with the scalars gives a nondegenerate form.** If the reflexive
bilinear map `B : V → Hom(V, Q)` is injective, `Q` is one-dimensional and `e : Q → K` is injective,
then `[u], [v] ↦ e (B u v)` is a nondegenerate bilinear form on the symplectic normal space of any
subspace `W`. -/
theorem IsRefl.nondegenerate_compr₂_symplecticNormalForm (hB : B.IsRefl)
    (hinj : Function.Injective B) (hQ : finrank K Q = 1) {e : Q →ₗ[K] K}
    (he : Function.Injective e) :
    BilinForm.Nondegenerate ((hB.symplecticNormalForm W).compr₂ e) := by
  refine (IsRefl.nondegenerate_iff_separatingLeft
    (hB.isRefl_symplecticNormalForm.compr₂_of_injective he)).2 fun x hx ↦
    hB.injective_symplecticNormalForm hinj hQ ?_
  rw [map_zero]
  ext y
  exact he (by simpa using hx (Submodule.Quotient.mk y))

/-- **Dimension of the symplectic normal space.** If the bilinear map `B : V → Hom(V, Q)` is
injective, `Q` is one-dimensional and `W` is isotropic, then
`dim (W^⊥ ⧸ W) + 2 dim W = dim V`. -/
theorem finrank_symplecticNormal_add_two_mul_finrank (hinj : Function.Injective B)
    (hQ : finrank K Q = 1) (hW : W ≤ W.orthogonalBilin B) :
    finrank K (SymplecticNormal B W) + 2 * finrank K W = finrank K V := by
  obtain ⟨e, hnd⟩ := exists_nondegenerate_compr₂_of_injective hinj hQ
  have horth := BilinForm.finrank_orthogonal hnd W
  rw [BilinForm.orthogonal, Submodule.orthogonalBilin_compr₂_of_injective e.injective] at horth
  have hquot : finrank K (SymplecticNormal B W) +
      finrank K (W.comap (W.orthogonalBilin B).subtype) = finrank K (W.orthogonalBilin B) :=
    Submodule.finrank_quotient_add_finrank _
  rw [LinearEquiv.finrank_eq (Submodule.comapSubtypeEquivOfLe hW)] at hquot
  have hle := Submodule.finrank_le W
  omega

/-- **The symplectic normal space of a half-dimensional isotropic subspace is zero.** If the
bilinear map `B : V → Hom(V, Q)` is injective, `Q` is one-dimensional and `W` is isotropic,
then the symplectic normal space `W^⊥ ⧸ W` is zero exactly when
`2 dim W = dim V`. -/
theorem subsingleton_symplecticNormal_iff (hinj : Function.Injective B) (hQ : finrank K Q = 1)
    (hW : W ≤ W.orthogonalBilin B) :
    Subsingleton (SymplecticNormal B W) ↔ 2 * finrank K W = finrank K V := by
  rw [← finrank_zero_iff (R := K), ← finrank_symplecticNormal_add_two_mul_finrank hinj hQ hW]
  omega

end Field

end LinearMap
