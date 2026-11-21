/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Bialgebra.MonoidAlgebra
public import TauCeti.Algebra.AlgebraicGroup.DeligneTorus.Splitting
public import TauCeti.Algebra.Bialgebra.BaseChange
public import TauCeti.RingTheory.TensorProduct.LiftEquiv

/-!
# The coordinate bialgebra of the complex Deligne torus

Over `ℂ` the Deligne torus `S = Res_{ℂ/ℝ} 𝔾ₘ` splits as `S_ℂ ≅ 𝔾ₘ × 𝔾ₘ`.
`TauCeti.DeligneTorus.complexSplitting` gives this splitting on points over complex algebras. This
file gives it on coordinate rings: the bialgebra isomorphism

```text
ℂ ⊗[ℝ] S ≃ₐc[ℂ] ℂ[ℤ²]
```

with the group algebra of `ℤ²`, written multiplicatively as `Multiplicative (ℤ × ℤ)`. The two
coordinates `z₁ = X^{(1,0)}` and `z₂ = X^{(0,1)}` of `𝔾ₘ × 𝔾ₘ` correspond to the two components of
the splitting, and the basis element `X^{(p,q)}` corresponds to the character
`TauCeti.DeligneTorus.characterGroup` of `(p, q)`, which is `(z₁, z₂) ↦ z₁ ^ p * z₂ ^ q`.

Thus the characters of `S_ℂ ≅ 𝔾ₘ × 𝔾ₘ` are the pairs `(p, q) ∈ ℤ²`. A representation of `S` on a
real vector space `V` is a comodule over `S`. After base change to `ℂ` it becomes a comodule over
`ℂ[ℤ²]`, that is, a `ℤ²`-grading of `ℂ ⊗[ℝ] V`. This grading gives the Hodge decomposition of the
representation, with the sign flip of the homology convention: the Hodge component `V^{p,q}`
(`TauCeti.DeligneTorus.hodgeComponent`) is the `(-p, -q)`-graded piece.

Complex conjugation of the coefficients composed with the swap `(p, q) ↦ (q, p)` of `ℤ²` is a real
algebra automorphism of `ℂ[ℤ²]` (`TauCeti.DeligneTorus.conjSwap`). It fixes the coordinate map of
the splitting (`TauCeti.DeligneTorus.conjSwap_comp_splittingPoint`). This is the coordinate form
of the fact that complex conjugation of `S(ℂ)` exchanges the two factors
(`TauCeti.DeligneTorus.complexSplitting_conj`).

## Main definitions

* `TauCeti.DeligneTorus.splittingPoint`: the `ℂ[ℤ²]`-valued point of `S` whose splitting is
  `(z₁, z₂)`.
* `TauCeti.DeligneTorus.splittingBialgEquiv`: the bialgebra isomorphism
  `ℂ ⊗[ℝ] S ≃ₐc[ℂ] ℂ[ℤ²]`, the `ℂ`-linear extension of `splittingPoint`.
* `TauCeti.DeligneTorus.conjSwap`: the real algebra automorphism
  `∑ c_{p,q} X^{(p,q)} ↦ ∑ conj c_{p,q} X^{(q,p)}` of `ℂ[ℤ²]`.

## Main results

* `TauCeti.DeligneTorus.complexSplitting_splittingPoint`: the splitting of `splittingPoint` is
  `(z₁, z₂)`.
* `TauCeti.DeligneTorus.characterGroup_splittingPoint`: the character `(p, q)` of
  `splittingPoint` is the basis element `X^{(p,q)}`.
* `TauCeti.DeligneTorus.splittingBialgEquiv_one_tmul`: the isomorphism restricts to
  `splittingPoint` on `S`.
* `TauCeti.DeligneTorus.splittingBialgEquiv_symm_single`: its inverse sends `X^{(p,q)}` to the
  character `(p, q)` of the universal point of `S`.
* `TauCeti.DeligneTorus.liftEquiv_splittingBialgEquiv_symm_single`: read through the inverse, a
  point of `S` sends `X^{(p,q)}` to its character `(p, q)`.
* `TauCeti.DeligneTorus.conjSwap_comp_splittingPoint`: `conjSwap` fixes `splittingPoint`.

## References

* J. S. Milne, *Introduction to Shimura varieties*, §2, *Hodge structures as representations of
  `S`*, p. 26.
* P. Deligne, *Travaux de Shimura*, Séminaire Bourbaki, exposé 389 (1971), §1.
-/

public section

open WithConv TauCeti.Algebra
open scoped TensorProduct

namespace TauCeti.DeligneTorus

/-! ### The universal point of `𝔾ₘ × 𝔾ₘ` -/

/-- **The coordinate point of the splitting**: the point of `S` with values in `ℂ[ℤ²]` whose
splitting is the pair of coordinates `(z₁, z₂) = (X^{(1,0)}, X^{(0,1)})` of `𝔾ₘ × 𝔾ₘ`. -/
noncomputable def splittingPoint : WithConv (S →ₐ[ℝ] MonoidAlgebra ℂ (Multiplicative (ℤ × ℤ))) :=
  (complexSplitting _).symm
    ((MonoidAlgebra.of ℂ (Multiplicative (ℤ × ℤ))).toHomUnits (.ofAdd (1, 0)),
      (MonoidAlgebra.of ℂ (Multiplicative (ℤ × ℤ))).toHomUnits (.ofAdd (0, 1)))

/-- The splitting of `splittingPoint` is the pair of coordinates `(z₁, z₂)`. -/
@[simp]
theorem complexSplitting_splittingPoint :
    complexSplitting _ splittingPoint =
      ((MonoidAlgebra.of ℂ (Multiplicative (ℤ × ℤ))).toHomUnits (.ofAdd (1, 0)),
        (MonoidAlgebra.of ℂ (Multiplicative (ℤ × ℤ))).toHomUnits (.ofAdd (0, 1))) :=
  MulEquiv.apply_symm_apply _ _

/-- **The character `(p, q)` of `splittingPoint` is `X^{(p,q)}`.** -/
@[simp]
theorem characterGroup_splittingPoint (pq : Multiplicative (ℤ × ℤ)) :
    (characterGroup _ pq splittingPoint : MonoidAlgebra ℂ (Multiplicative (ℤ × ℤ))) =
      MonoidAlgebra.single pq 1 := by
  obtain ⟨⟨p, q⟩, rfl⟩ : ∃ pq' : ℤ × ℤ, Multiplicative.ofAdd pq' = pq := ⟨pq.toAdd, rfl⟩
  have hpq : Multiplicative.ofAdd ((1 : ℤ), (0 : ℤ)) ^ p *
      Multiplicative.ofAdd ((0 : ℤ), (1 : ℤ)) ^ q = Multiplicative.ofAdd (p, q) := by
    rw [← ofAdd_zsmul, ← ofAdd_zsmul, ← ofAdd_add]
    simp
  simp [characterGroup_apply, ← map_zpow, ← map_mul, hpq]

/-- For a complex algebra map `χ : ℂ[ℤ²] → R`, the point `χ ∘ splittingPoint` of `S` has
splitting `(χ z₁, χ z₂)`. -/
private theorem complexSplitting_mapValue_splittingPoint {R : Type*} [CommRing R] [Algebra ℝ R]
    [Algebra ℂ R] [IsScalarTower ℝ ℂ R] (χ : MonoidAlgebra ℂ (Multiplicative (ℤ × ℤ)) →ₐ[ℂ] R) :
    complexSplitting R (AlgHom.mapValue (χ.restrictScalars ℝ) splittingPoint) =
      (Units.map (χ : _ →* R)
          ((MonoidAlgebra.of ℂ (Multiplicative (ℤ × ℤ))).toHomUnits (.ofAdd (1, 0))),
        Units.map (χ : _ →* R)
          ((MonoidAlgebra.of ℂ (Multiplicative (ℤ × ℤ))).toHomUnits (.ofAdd (0, 1)))) := by
  rw [complexSplitting_mapValue, complexSplitting_splittingPoint]

/-! ### The bialgebra isomorphism `ℂ ⊗[ℝ] S ≃ ℂ[ℤ²]` -/

/-- The `ℂ`-linear extension of a point `f` of `S`, evaluated at the universal point `1 ⊗ id` of
`S` in `ℂ ⊗[ℝ] S`, is `f`. -/
private theorem mapValue_liftEquiv_includeRight {R : Type*} [CommRing R] [Algebra ℝ R]
    [Algebra ℂ R] [IsScalarTower ℝ ℂ R] (f : S →ₐ[ℝ] R) :
    AlgHom.mapValue ((AlgHom.liftEquiv ℝ ℂ S R f).restrictScalars ℝ)
      (toConv (Algebra.TensorProduct.includeRight (R := ℝ) (A := ℂ) (B := S))) = toConv f := by
  rw [AlgHom.mapValue_apply, ofConv_toConv, AlgHom.liftEquiv_comp_includeRight]

/-- The `ℂ`-algebra map `ℂ ⊗[ℝ] S → ℂ[ℤ²]` extending `splittingPoint`. -/
private noncomputable def splittingAlgHom :
    ℂ ⊗[ℝ] S →ₐ[ℂ] MonoidAlgebra ℂ (Multiplicative (ℤ × ℤ)) :=
  AlgHom.liftEquiv ℝ ℂ S _ splittingPoint.ofConv

/-- The universal point of `S` with values in `ℂ ⊗[ℝ] S`. -/
private noncomputable def universalPoint : WithConv (S →ₐ[ℝ] ℂ ⊗[ℝ] S) :=
  toConv Algebra.TensorProduct.includeRight

/-- The `ℂ`-algebra map `ℂ[ℤ²] → ℂ ⊗[ℝ] S` sending `X^{(p,q)}` to the character `(p, q)` of the
universal point. -/
private noncomputable def splittingInvAlgHom :
    MonoidAlgebra ℂ (Multiplicative (ℤ × ℤ)) →ₐ[ℂ] ℂ ⊗[ℝ] S :=
  MonoidAlgebra.lift ℂ _ _
    ((Units.coeHom _).comp
      ((MonoidHom.eval (N := (ℂ ⊗[ℝ] S)ˣ) universalPoint).comp (characterGroup (ℂ ⊗[ℝ] S))))

private theorem splittingInvAlgHom_single (pq : Multiplicative (ℤ × ℤ)) :
    splittingInvAlgHom (MonoidAlgebra.single pq 1) = characterGroup _ pq universalPoint := by
  simp [splittingInvAlgHom]

private theorem mapValue_splittingAlgHom_universalPoint :
    AlgHom.mapValue (splittingAlgHom.restrictScalars ℝ) universalPoint = splittingPoint := by
  rw [splittingAlgHom, universalPoint, mapValue_liftEquiv_includeRight, toConv_ofConv]

private theorem splittingAlgHom_comp_splittingInvAlgHom :
    splittingAlgHom.comp splittingInvAlgHom = AlgHom.id ℂ _ := by
  refine MonoidAlgebra.algHom_ext (fun pq ↦ ?_) (Subsingleton.elim _ _)
  rw [AlgHom.comp_apply, splittingInvAlgHom_single, AlgHom.id_apply]
  have h := characterGroup_mapValue (R := ℂ ⊗[ℝ] S)
    (R' := MonoidAlgebra ℂ (Multiplicative (ℤ × ℤ))) splittingAlgHom pq universalPoint
  rw [mapValue_splittingAlgHom_universalPoint] at h
  rw [← characterGroup_splittingPoint, h, Units.coe_map, MonoidHom.coe_ofClass]

private theorem splittingInvAlgHom_comp_splittingAlgHom :
    splittingInvAlgHom.comp splittingAlgHom = AlgHom.id ℂ _ := by
  refine (AlgHom.liftEquiv ℝ ℂ S _).symm.injective ?_
  have key : AlgHom.mapValue (splittingInvAlgHom.restrictScalars ℝ) splittingPoint =
      universalPoint := by
    apply (complexSplitting _).injective
    rw [complexSplitting_mapValue_splittingPoint]
    have h₁ := splittingInvAlgHom_single (.ofAdd (1, 0))
    have h₂ := splittingInvAlgHom_single (.ofAdd (0, 1))
    rw [characterGroup_apply, zpow_one, zpow_zero, mul_one] at h₁
    rw [characterGroup_apply, zpow_one, zpow_zero, one_mul] at h₂
    ext <;> simp only [Units.coe_map, MonoidHom.coe_ofClass, MonoidHom.coe_toHomUnits,
      MonoidAlgebra.of_apply] <;> assumption
  have key' := congrArg ofConv key
  rw [AlgHom.mapValue_apply, ofConv_toConv, universalPoint, ofConv_toConv] at key'
  exact AlgHom.ext fun s ↦ by simpa [splittingAlgHom] using DFunLike.congr_fun key' s

/-- The convolution of the two images of `splittingPoint` under the coordinate inclusions
`ℂ[ℤ²] → ℂ[ℤ²] ⊗ ℂ[ℤ²]`. -/
private noncomputable def splittingPointConv :
    WithConv (S →ₐ[ℝ] MonoidAlgebra ℂ (Multiplicative (ℤ × ℤ)) ⊗[ℂ]
      MonoidAlgebra ℂ (Multiplicative (ℤ × ℤ))) :=
  AlgHom.mapValue ((Algebra.TensorProduct.includeLeft (S := ℂ)
      (A := MonoidAlgebra ℂ (Multiplicative (ℤ × ℤ)))
      (B := MonoidAlgebra ℂ (Multiplicative (ℤ × ℤ)))).restrictScalars ℝ) splittingPoint *
    AlgHom.mapValue ((Algebra.TensorProduct.includeRight (R := ℂ)
      (A := MonoidAlgebra ℂ (Multiplicative (ℤ × ℤ)))
      (B := MonoidAlgebra ℂ (Multiplicative (ℤ × ℤ)))).restrictScalars ℝ) splittingPoint

/-- Applied to the comultiplication of `1 ⊗ s`, the square of `splittingAlgHom` is the convolution
of the two images of `splittingPoint` under the coordinate inclusions `ℂ[ℤ²] → ℂ[ℤ²] ⊗ ℂ[ℤ²]`. -/
private theorem map_splittingAlgHom_comul_one_tmul (s : S) :
    Algebra.TensorProduct.map splittingAlgHom splittingAlgHom
        (Bialgebra.comulAlgHom ℂ (ℂ ⊗[ℝ] S) (1 ⊗ₜ s)) =
      splittingPointConv.ofConv s := by
  rw [splittingPointConv, TensorProduct.comulAlgHom_baseChange, Algebra.TensorProduct.map_tmul,
    AlgHom.id_apply, AlgHom.convMul_apply, Bialgebra.comulAlgHom_apply]
  induction (Coalgebra.comul s : S ⊗[ℝ] S) using TensorProduct.inductionOn with
  | add y z hy hz => simp only [TensorProduct.tmul_add, map_add, hy, hz]
  | tmul a b => simp [splittingAlgHom, Algebra.TensorProduct.tmul_mul_tmul]

private theorem splittingAlgHom_comul :
    (Algebra.TensorProduct.map splittingAlgHom splittingAlgHom).comp
        (Bialgebra.comulAlgHom ℂ (ℂ ⊗[ℝ] S)) =
      (Bialgebra.comulAlgHom ℂ _).comp splittingAlgHom := by
  refine (AlgHom.liftEquiv ℝ ℂ S _).symm.injective ?_
  have key : splittingPointConv =
      AlgHom.mapValue ((Bialgebra.comulAlgHom ℂ _).restrictScalars ℝ) splittingPoint := by
    apply (complexSplitting _).injective
    rw [splittingPointConv, map_mul, complexSplitting_mapValue_splittingPoint,
      complexSplitting_mapValue_splittingPoint, complexSplitting_mapValue_splittingPoint]
    ext <;> simp [Algebra.TensorProduct.tmul_mul_tmul]
  refine AlgHom.ext fun s ↦ ?_
  have h := (map_splittingAlgHom_comul_one_tmul s).trans
    (congrArg (fun f : WithConv (S →ₐ[ℝ] _) ↦ f.ofConv s) key)
  rw [AlgHom.liftEquiv_symm_apply, AlgHom.liftEquiv_symm_apply, AlgHom.comp_apply,
    AlgHom.comp_apply, h]
  simp [splittingAlgHom]

private theorem splittingAlgHom_counit :
    (Bialgebra.counitAlgHom ℂ _).comp splittingAlgHom = Bialgebra.counitAlgHom ℂ (ℂ ⊗[ℝ] S) := by
  refine (AlgHom.liftEquiv ℝ ℂ S _).symm.injective ?_
  have key :
      AlgHom.mapValue ((Bialgebra.counitAlgHom ℂ _).restrictScalars ℝ) splittingPoint = 1 := by
    apply (complexSplitting _).injective
    rw [complexSplitting_mapValue_splittingPoint, map_one]
    ext <;> simp
  refine AlgHom.ext fun s ↦ ?_
  simpa [splittingAlgHom] using congrArg (fun f : WithConv (S →ₐ[ℝ] ℂ) ↦ f.ofConv s) key

/-- `splittingAlgHom` as a bialgebra map. -/
private noncomputable def splittingBialgHom :
    ℂ ⊗[ℝ] S →ₐc[ℂ] MonoidAlgebra ℂ (Multiplicative (ℤ × ℤ)) :=
  -- the named arguments keep elaboration from unfolding the Weil restriction instances
  BialgHom.ofAlgHom (R := ℂ) (A := ℂ ⊗[ℝ] S) (B := MonoidAlgebra ℂ (Multiplicative (ℤ × ℤ)))
    splittingAlgHom splittingAlgHom_counit splittingAlgHom_comul

private theorem splittingBialgHom_apply (x : ℂ ⊗[ℝ] S) :
    splittingBialgHom x = splittingAlgHom x :=
  BialgHom.ofAlgHom_apply _ _ _ x

private theorem splittingBialgHom_bijective : Function.Bijective splittingBialgHom := by
  rw [show ⇑splittingBialgHom = ⇑splittingAlgHom from funext splittingBialgHom_apply]
  exact ⟨Function.LeftInverse.injective (g := splittingInvAlgHom) fun x ↦ by
      rw [← AlgHom.comp_apply, splittingInvAlgHom_comp_splittingAlgHom, AlgHom.id_apply],
    Function.RightInverse.surjective (g := splittingInvAlgHom) fun x ↦ by
      rw [← AlgHom.comp_apply, splittingAlgHom_comp_splittingInvAlgHom, AlgHom.id_apply]⟩

/-- **The splitting of the Deligne torus on coordinate rings**: the bialgebra isomorphism
`ℂ ⊗[ℝ] S ≃ₐc[ℂ] ℂ[ℤ²]` with the group algebra of `ℤ²`. It is the `ℂ`-linear extension of
`splittingPoint` (`splittingBialgEquiv_one_tmul`), and the coordinate form of
`S_ℂ ≅ 𝔾ₘ × 𝔾ₘ`. -/
noncomputable def splittingBialgEquiv :
    ℂ ⊗[ℝ] S ≃ₐc[ℂ] MonoidAlgebra ℂ (Multiplicative (ℤ × ℤ)) :=
  BialgEquiv.ofBijective (R := ℂ) (A := ℂ ⊗[ℝ] S) (B := MonoidAlgebra ℂ (Multiplicative (ℤ × ℤ)))
    splittingBialgHom splittingBialgHom_bijective

private theorem splittingBialgEquiv_apply (x : ℂ ⊗[ℝ] S) :
    splittingBialgEquiv x = splittingAlgHom x := by
  rw [splittingBialgEquiv, BialgEquiv.coe_ofBijective, splittingBialgHom_apply]

/-- On `S` the isomorphism `splittingBialgEquiv` is the coordinate point `splittingPoint`. -/
@[simp]
theorem splittingBialgEquiv_one_tmul (s : S) :
    splittingBialgEquiv (1 ⊗ₜ s) = splittingPoint.ofConv s := by
  simp [splittingBialgEquiv_apply, splittingAlgHom]

/-- `splittingBialgEquiv` is the `ℂ`-linear extension of `splittingPoint`. -/
theorem splittingBialgEquiv_toAlgHom :
    (splittingBialgEquiv : ℂ ⊗[ℝ] S →ₐ[ℂ] MonoidAlgebra ℂ (Multiplicative (ℤ × ℤ))) =
      AlgHom.liftEquiv ℝ ℂ S _ splittingPoint.ofConv :=
  AlgHom.ext splittingBialgEquiv_apply

/-- The inverse of `splittingBialgEquiv` sends `X^{(p,q)}` to the character `(p, q)` of the
universal point `1 ⊗ id` of `S` in `ℂ ⊗[ℝ] S`. -/
@[simp]
theorem splittingBialgEquiv_symm_single (pq : Multiplicative (ℤ × ℤ)) :
    splittingBialgEquiv.symm (MonoidAlgebra.single pq 1) =
      characterGroup _ pq
        (toConv (Algebra.TensorProduct.includeRight (R := ℝ) (A := ℂ) (B := S))) := by
  have h := splittingInvAlgHom_single pq
  rw [universalPoint] at h
  rw [← h, ← splittingBialgEquiv.symm_apply_apply (splittingInvAlgHom _)]
  congr 1
  rw [splittingBialgEquiv_apply, ← AlgHom.comp_apply, splittingAlgHom_comp_splittingInvAlgHom,
    AlgHom.id_apply]

/-- **A point of `S` sends `X^{(p,q)}` to its character `(p, q)`**: for a point `g` of `S` with
values in a complex algebra `R`, the `ℂ`-algebra map `ℂ[ℤ²] → R` obtained from `g` through the
inverse of `splittingBialgEquiv` sends `X^{(p,q)}` to `characterGroup R (p, q) g`. -/
theorem liftEquiv_splittingBialgEquiv_symm_single {R : Type*} [CommRing R] [Algebra ℝ R]
    [Algebra ℂ R] [IsScalarTower ℝ ℂ R] (g : WithConv (S →ₐ[ℝ] R))
    (pq : Multiplicative (ℤ × ℤ)) :
    AlgHom.liftEquiv ℝ ℂ S R g.ofConv (splittingBialgEquiv.symm (MonoidAlgebra.single pq 1)) =
      characterGroup R pq g := by
  have h := characterGroup_mapValue (AlgHom.liftEquiv ℝ ℂ S R g.ofConv) pq
    (toConv (Algebra.TensorProduct.includeRight (R := ℝ) (A := ℂ) (B := S)))
  rw [mapValue_liftEquiv_includeRight, toConv_ofConv] at h
  rw [splittingBialgEquiv_symm_single, h, Units.coe_map, MonoidHom.coe_ofClass]

/-! ### Complex conjugation -/

/-- The automorphism `(p, q) ↦ (q, p)` of `ℤ²`. -/
private def swapMulEquiv : Multiplicative (ℤ × ℤ) ≃* Multiplicative (ℤ × ℤ) :=
  AddEquiv.toMultiplicative (AddEquiv.prodComm (M := ℤ) (N := ℤ))

/-- **Complex conjugation on `ℂ[ℤ²]`**: the real algebra automorphism
`∑ c_{p,q} X^{(p,q)} ↦ ∑ conj c_{p,q} X^{(q,p)}`, which conjugates the coefficients and swaps the
two coordinates `z₁` and `z₂`. -/
noncomputable def conjSwap :
    MonoidAlgebra ℂ (Multiplicative (ℤ × ℤ)) ≃ₐ[ℝ] MonoidAlgebra ℂ (Multiplicative (ℤ × ℤ)) :=
  (MonoidAlgebra.mapAlgEquiv ℝ _ Complex.conjAe).trans (MonoidAlgebra.domCongr ℝ ℂ swapMulEquiv)

@[simp]
theorem conjSwap_single (p q : ℤ) (c : ℂ) :
    conjSwap (MonoidAlgebra.single (.ofAdd (p, q)) c) =
      MonoidAlgebra.single (.ofAdd (q, p)) (starRingEnd ℂ c) := by
  simp [conjSwap, swapMulEquiv, Complex.conjAe_coe]

/-- `conjSwap` conjugates the constants. -/
@[simp]
theorem conjSwap_single_one (c : ℂ) :
    conjSwap (MonoidAlgebra.single 1 c) = MonoidAlgebra.single 1 (starRingEnd ℂ c) :=
  conjSwap_single 0 0 c

/-- `conjSwap` is conjugate-linear over `ℂ`. -/
theorem conjSwap_smul (c : ℂ) (x : MonoidAlgebra ℂ (Multiplicative (ℤ × ℤ))) :
    conjSwap (c • x) = starRingEnd ℂ c • conjSwap x := by
  induction x using MonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy => simp only [smul_add, map_add, hx, hy]
  | single m a =>
    obtain ⟨⟨p, q⟩, rfl⟩ : ∃ pq : ℤ × ℤ, Multiplicative.ofAdd pq = m := ⟨m.toAdd, rfl⟩
    simp [MonoidAlgebra.smul_single]

/-- `conjSwap` is an involution. -/
@[simp]
theorem conjSwap_conjSwap (x : MonoidAlgebra ℂ (Multiplicative (ℤ × ℤ))) :
    conjSwap (conjSwap x) = x := by
  induction x using MonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | single m a =>
    obtain ⟨⟨p, q⟩, rfl⟩ : ∃ pq : ℤ × ℤ, Multiplicative.ofAdd pq = m := ⟨m.toAdd, rfl⟩
    simp

/-- **`conjSwap` fixes `splittingPoint`.** On coordinate rings, this says that complex
conjugation of `S(ℂ)` exchanges the two factors of the splitting
(`TauCeti.DeligneTorus.complexSplitting_conj`). -/
@[simp]
theorem conjSwap_comp_splittingPoint :
    (conjSwap : MonoidAlgebra ℂ (Multiplicative (ℤ × ℤ)) →ₐ[ℝ] _).comp splittingPoint.ofConv =
      splittingPoint.ofConv := by
  have key : AlgHom.mapValue (conjSwap : MonoidAlgebra ℂ (Multiplicative (ℤ × ℤ)) →ₐ[ℝ] _)
      splittingPoint = splittingPoint := by
    apply (pointsMulEquiv _).injective
    rw [pointsMulEquiv_mapValue]
    ext1
    apply (complexTensorProductEquivProd _).injective
    rw [Units.coe_map, MonoidHom.coe_ofClass,
      complexTensorProductEquivProd_lTensor_of_map_smul _ conjSwap_smul]
    have hu : complexTensorProductEquivProd _
          (pointsMulEquiv _ splittingPoint : ℂ ⊗[ℝ] MonoidAlgebra ℂ (Multiplicative (ℤ × ℤ))) =
        (MonoidAlgebra.single (Multiplicative.ofAdd ((1 : ℤ), (0 : ℤ))) (1 : ℂ),
          MonoidAlgebra.single (Multiplicative.ofAdd ((0 : ℤ), (1 : ℤ))) (1 : ℂ)) := by
      have h₁ := coe_complexSplitting_fst splittingPoint
      have h₂ := coe_complexSplitting_snd splittingPoint
      rw [complexSplitting_splittingPoint] at h₁ h₂
      exact Prod.ext (h₁.symm.trans (by simp)) (h₂.symm.trans (by simp))
    rw [hu]
    simp
  simpa using congrArg ofConv key

end TauCeti.DeligneTorus
