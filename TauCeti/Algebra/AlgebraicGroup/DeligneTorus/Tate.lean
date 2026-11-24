/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.HopfAlgebra.GroupLike
public import TauCeti.Algebra.AlgebraicGroup.DeligneTorus.Hodge
public import TauCeti.Algebra.Coalgebra.Comodule.Trivial
import TauCeti.Algebra.Coalgebra.Convolution

/-!
# The norm character and the Tate comodules of the Deligne torus

The norm `Nm : S → 𝔾ₘ` of the Deligne torus `S = Res_{ℂ/ℝ} 𝔾ₘ` is a character, so it is a
group-like element of the coordinate Hopf algebra `S`: by the Yoneda lemma it is the norm of the
universal point of `S`. A group-like element `χ` makes every real vector space `M` a comodule, with
coaction `v ↦ v ⊗ χ` (`TauCeti.Comodule.groupLike`). For `χ = Nm ^ m` this is the Tate comodule
`ℝ(m)`, on which a point `g` of `S` acts by the scalar `Nm(g) ^ m`. On real points
`z ∈ S(ℝ) = ℂˣ` this is `|z| ^ (2 * m) = z ^ m * conj z ^ m`, so in the homology convention of
`TauCeti.DeligneTorus.hodgeComponent` the Tate comodule has the single Hodge type `(-m, -m)` and
is pure of weight `-2 * m`, matching the Tate Hodge structure `TauCeti.Hodge.tate`.

Over a complex algebra `R`, where `S(R) ≃ Rˣ × Rˣ` (`TauCeti.DeligneTorus.complexSplitting`), the
norm of a point with coordinates `(z₁, z₂)` is `z₁ * z₂`, the character `(1, 1)`
(`TauCeti.DeligneTorus.norm_eq_characterGroup`). This is what pins the Hodge type.

## Main definitions

* `TauCeti.DeligneTorus.normUnit`: the norm character, as a unit of `S`.
* `TauCeti.DeligneTorus.normGroupLike`: the norm character, as a group-like element of `S`.
* `TauCeti.DeligneTorus.tateComodule M m`: the comodule structure `v ↦ v ⊗ Nm ^ m` on a real
  vector space `M`; for `M = ℝ` it is the one-dimensional Tate comodule `ℝ(m)`.

## Main results

* `TauCeti.DeligneTorus.apply_normUnit`: a point `g` of `S` sends the norm character to `Nm(g)`.
* `TauCeti.DeligneTorus.norm_eq_characterGroup`: over a complex algebra the norm is the character
  `(z₁, z₂) ↦ z₁ * z₂`.
* `TauCeti.DeligneTorus.endOfPoint_tateComodule`: a point `g` acts on `ℝ(m)` by `Nm(g) ^ m`.
* `TauCeti.DeligneTorus.hodgeComponent_tateComodule`: the Tate comodule has the single Hodge type
  `(-m, -m)`.
* `TauCeti.DeligneTorus.isHodgeDecomposition_tateComodule`: its Hodge components form a Hodge
  decomposition of weight `-2 * m`.

## References

* J. S. Milne, *Introduction to Shimura varieties*, §2, *Hodge structures as representations of
  `S`*, pp. 26–27.
* P. Deligne, *Travaux de Shimura*, Séminaire Bourbaki, exposé 389 (1971), §1.
-/

public section

open WithConv TauCeti.Algebra
open scoped TensorProduct

namespace TauCeti.DeligneTorus

/-! ### The norm character -/

/-- **The norm character** `Nm : S → 𝔾ₘ`, as a unit of the coordinate ring `S`: the norm of the
universal point of `S`. A point `g` of `S` sends it to `Nm(g)` (`apply_normUnit`). -/
noncomputable def normUnit : Sˣ :=
  norm S (toConv (AlgHom.id ℝ S))

/-- **A point of `S` sends the norm character to its norm.** -/
theorem apply_normUnit {R : Type*} [CommRing R] [Algebra ℝ R] (g : WithConv (S →ₐ[ℝ] R)) :
    g.ofConv (normUnit : S) = (norm R g : R) := by
  have h := norm_mapValue g.ofConv (toConv (AlgHom.id ℝ S))
  rw [AlgHom.mapValue_apply, ofConv_toConv, AlgHom.comp_id, toConv_ofConv] at h
  rw [h, Units.coe_map, MonoidHom.coe_ofClass, normUnit]

/-- **The norm character is group-like**: `ε(Nm) = 1` and `Δ(Nm) = Nm ⊗ Nm`. -/
theorem isGroupLikeElem_normUnit : IsGroupLikeElem ℝ (normUnit : S) where
  counit_eq_one := by
    have h := apply_normUnit (R := ℝ) 1
    rwa [TauCeti.Bialgebra.ofConv_one_eq_counitAlgHom, map_one, Units.val_one,
      Bialgebra.counitAlgHom_apply] at h
  comul_eq_tmul_self := by
    have h := apply_normUnit (toConv (Bialgebra.comulAlgHom ℝ S))
    rw [ofConv_toConv, Bialgebra.comulAlgHom_apply, TauCeti.Bialgebra.comulPoint_eq_include_mul,
      map_mul, Units.val_mul, ← apply_normUnit, ← apply_normUnit, ofConv_toConv,
      ofConv_toConv, Algebra.TensorProduct.includeLeft_apply,
      Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.tmul_mul_tmul, mul_one,
      one_mul] at h
    exact h

/-- **The norm character** `Nm : S → 𝔾ₘ`, as a group-like element of the coordinate Hopf
algebra `S`. -/
noncomputable def normGroupLike : GroupLike ℝ S :=
  ⟨normUnit, isGroupLikeElem_normUnit⟩

@[simp]
theorem val_normGroupLike : (normGroupLike : S) = normUnit :=
  (rfl)

/-- The unit underlying a power of the norm character is the power of `normUnit`. -/
theorem val_normGroupLike_zpow (m : ℤ) :
    ((normGroupLike ^ m : GroupLike ℝ S) : S) = ((normUnit ^ m : Sˣ) : S) := by
  have h : GroupLike.toUnits ℝ normGroupLike = normUnit := Units.ext rfl
  rw [← h, ← map_zpow]
  rfl

/-- **A point of `S` sends `Nm ^ m` to the `m`-th power of its norm.** -/
theorem apply_normGroupLike_zpow {R : Type*} [CommRing R] [Algebra ℝ R]
    (g : WithConv (S →ₐ[ℝ] R)) (m : ℤ) :
    g.ofConv ((normGroupLike ^ m : GroupLike ℝ S) : S) = ((norm R g ^ m : Rˣ) : R) := by
  have h : Units.map (g.ofConv : S →* R) normUnit = norm R g :=
    Units.ext (by rw [Units.coe_map, MonoidHom.coe_ofClass, apply_normUnit])
  rw [val_normGroupLike_zpow, ← h, ← map_zpow, Units.coe_map, MonoidHom.coe_ofClass]

/-! ### The norm over a complex algebra -/

section Complex

variable {R : Type*} [CommRing R] [Algebra ℝ R] [Algebra ℂ R] [IsScalarTower ℝ ℂ R]

omit [Algebra ℝ R] [Algebra ℂ R] [IsScalarTower ℝ ℂ R] in
/-- The algebra norm of `R × R` over `R` is the product of the two components. -/
private theorem norm_prod_mk (a b : R) : Algebra.norm R ((a, b) : R × R) = a * b := by
  have h : Algebra.lmul R (R × R) (a, b) =
      LinearMap.prodMap (Algebra.lmul R R a) (Algebra.lmul R R b) := by
    ext <;> simp
  rw [Algebra.norm_apply, h, LinearMap.det_prodMap, ← Algebra.norm_apply, ← Algebra.norm_apply,
    Algebra.norm_self, MonoidHom.id_apply, MonoidHom.id_apply]

/-- **The norm over a complex algebra**: a point of `S` with coordinates `(z₁, z₂)` in
`S(R) ≃ Rˣ × Rˣ` has norm `z₁ * z₂`. -/
theorem coe_norm_eq_mul (f : WithConv (S →ₐ[ℝ] R)) :
    (norm R f : R) = (complexSplitting R f).1 * (complexSplitting R f).2 := by
  -- `R ⊗[ℝ] ℂ ≃ₐ[R] R × R`, `x ⊗ a ↦ (a • x, conj a • x)`; the type is not written out, since
  -- with `Algebra ℂ R` in scope the notation `R ⊗[ℝ] ℂ` would pick the real structure of `ℂ`
  let e := AlgEquiv.ofRingEquiv (R := R)
    (f := ((Algebra.TensorProduct.comm ℝ ℂ R).symm.trans
      (complexTensorProductEquivProd R)).toRingEquiv)
    fun r ↦ by simp [Algebra.TensorProduct.algebraMap_apply]
  rw [norm_apply, NormTorus.coe_norm, ← Algebra.norm_eq_of_algEquiv e,
    coe_complexSplitting_fst, coe_complexSplitting_snd, ← norm_prod_mk, Prod.mk.eta]
  exact congrArg (fun x ↦ Algebra.norm R (complexTensorProductEquivProd R x))
    ((Algebra.TensorProduct.comm ℝ ℂ R).symm_apply_apply _)

/-- **The norm is the character `(1, 1)`** of `S(R) ≃ Rˣ × Rˣ`, `(z₁, z₂) ↦ z₁ * z₂`. -/
theorem norm_eq_characterGroup (f : WithConv (S →ₐ[ℝ] R)) :
    norm R f = characterGroup R (.ofAdd (1, 1)) f :=
  Units.ext <| by rw [coe_norm_eq_mul, characterGroup_apply, zpow_one, zpow_one, Units.val_mul]

/-- The `m`-th power of the norm is the character `(m, m)`. -/
theorem norm_zpow_eq_characterGroup (f : WithConv (S →ₐ[ℝ] R)) (m : ℤ) :
    norm R f ^ m = characterGroup R (.ofAdd (m, m)) f := by
  rw [norm_eq_characterGroup, characterGroup_apply, characterGroup_apply, zpow_one, zpow_one,
    mul_zpow]

end Complex

/-- The coordinate point `splittingPoint` of `S` sends `Nm ^ m` to `X^{(m,m)}`. -/
theorem splittingPoint_normGroupLike_zpow (m : ℤ) :
    splittingPoint.ofConv ((normGroupLike ^ m : GroupLike ℝ S) : S) =
      MonoidAlgebra.single (Multiplicative.ofAdd (m, m)) (1 : ℂ) := by
  rw [apply_normGroupLike_zpow, norm_zpow_eq_characterGroup, characterGroup_splittingPoint]

/-! ### The Tate comodules -/

section Comodule

variable (M : Type*) [AddCommMonoid M] [Module ℝ M]

/-- **The Tate comodule** `ℝ(m)`: the comodule structure on a real vector space `M` with
coaction `v ↦ v ⊗ Nm ^ m`, for the norm character `Nm`. A point `g` of `S` acts on it by
`Nm(g) ^ m` (`endOfPoint_tateComodule`), and it has the single Hodge type `(-m, -m)`
(`hodgeComponent_tateComodule`). For `M = ℝ` it is the one-dimensional Tate comodule. -/
noncomputable abbrev tateComodule (m : ℤ) : Comodule ℝ S M :=
  Comodule.groupLike (R := ℝ) (C := S) (M := M) (normGroupLike ^ m)

variable {M}

/-- The coaction of the Tate comodule `ℝ(m)` is `v ↦ v ⊗ Nm ^ m`. -/
theorem tateComodule_coact_apply (m : ℤ) (v : M) :
    (tateComodule M m).coact v =
      v ⊗ₜ[ℝ] ((normGroupLike ^ m : GroupLike ℝ S) : S) :=
  (rfl)

/-- **A point of `S` acts on `ℝ(m)` by the `m`-th power of its norm.** -/
theorem endOfPoint_tateComodule {R : Type*} [CommRing R] [Algebra ℝ R]
    (g : WithConv (S →ₐ[ℝ] R)) (m : ℤ) :
    letI := tateComodule M m
    Comodule.endOfPoint M g.ofConv = ((norm R g ^ m : Rˣ) : R) • LinearMap.id := by
  rw [Comodule.endOfPoint_groupLike, apply_normGroupLike_zpow]

/-- **A real point `z ∈ S(ℝ) = ℂˣ` acts on `ℝ(m)` by `|z| ^ (2 * m)`**, the `m`-th power of the
squared modulus. -/
theorem endOfPoint_real_tateComodule (f : WithConv (S →ₐ[ℝ] ℝ)) (m : ℤ) :
    letI := tateComodule M m
    Comodule.endOfPoint M f.ofConv =
      (Complex.normSq (realPointsMulEquiv f) ^ m : ℝ) • LinearMap.id := by
  rw [endOfPoint_tateComodule, Units.val_zpow_eq_zpow_val, coe_norm_real]

end Comodule

/-! ### The Hodge type of the Tate comodules -/

variable {M : Type*} [AddCommGroup M] [Module ℝ M]

/-- Every vector of the complexified Tate comodule `ℂ ⊗ ℝ(m)` has Hodge type `(-m, -m)`. -/
private theorem hodgeComponent_tateComodule_neg (m : ℤ) :
    letI := tateComodule M m
    hodgeComponent M (-m) (-m) = ⊤ := by
  let _ := tateComodule M m
  refine eq_top_iff.2 fun v _ ↦ mem_hodgeComponent_iff.2 ?_
  rw [Comodule.endOfPoint_groupLike, splittingPoint_normGroupLike_zpow, neg_neg]
  rfl

/-- **The Hodge type of the Tate comodule**: `ℂ ⊗ ℝ(m)` is its own Hodge component `V^{-m,-m}`,
and every other Hodge component vanishes. -/
theorem hodgeComponent_tateComodule (m p q : ℤ) :
    letI := tateComodule M m
    hodgeComponent M p q = if p = -m ∧ q = -m then ⊤ else ⊥ := by
  let _ := tateComodule M m
  split_ifs with h
  · rw [h.1, h.2, hodgeComponent_tateComodule_neg]
  · have hne : (p, q) ≠ (-m, -m) := fun h' ↦ h (Prod.mk.inj h')
    have hdisj := (isInternal_hodgeComponent M).submodule_iSupIndep.pairwiseDisjoint hne
    simp only [Function.onFun, hodgeComponent_tateComodule_neg] at hdisj
    exact disjoint_top.1 hdisj

/-- **The Tate comodule is pure of weight `-2 * m`**: the components `p ↦ V^{p, -2m - p}` form a
Hodge decomposition of weight `-2 * m`. With `M = ℝ` this is the Hodge structure `ℝ(m)`. -/
theorem isHodgeDecomposition_tateComodule (m : ℤ) :
    letI := tateComodule M m
    Hodge.IsHodgeDecomposition (Hodge.complexificationConjugation M) (-2 * m)
      fun p ↦ hodgeComponent M p (-2 * m - p) := by
  let _ := tateComodule M m
  refine ⟨?_, fun p ↦ by rw [map_conj_hodgeComponent, sub_sub_cancel],
    ⟨-m, fun p hp ↦ by
      rw [hodgeComponent_tateComodule, ite_eq_right_iff.2 fun h ↦ absurd h (by omega)]⟩⟩
  have h := isInternal_hodgeComponent M
  rw [DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top] at h ⊢
  refine ⟨h.1.comp (f := fun p : ℤ ↦ (p, -2 * m - p)) fun p p' hp ↦ congrArg Prod.fst hp,
    eq_top_iff.2 (le_iSup_of_le (-m) ?_)⟩
  rw [hodgeComponent_tateComodule, ite_eq_left_iff.2 fun h ↦ absurd ⟨rfl, by ring⟩ h]

end TauCeti.DeligneTorus
