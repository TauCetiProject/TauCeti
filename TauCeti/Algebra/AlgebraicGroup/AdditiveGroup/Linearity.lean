/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.AdditiveGroup.Basic
import TauCeti.Algebra.Polynomial.Doubling
import Mathlib.Algebra.Polynomial.AlgebraMap

/-!
# Actions on vector groups in characteristic zero are linear

Let `R` be a commutative `ℚ`-algebra and `M` an `R`-module, with vector group
`V(M) = Spec (SymmetricAlgebra R M)`, whose `A`-valued points are the `R`-linear maps
`M →ₗ[R] A` (`TauCeti.AdditiveGroup.pointsMulEquiv`). Every endomorphism of the group functor of
`V(M)` that is natural in the value algebra `A` is `A`-linear on `M →ₗ[R] A`, and the same holds
for natural families of such endomorphisms parametrized by the points of an affine scheme
`Spec H`. Consequently an action of an affine group `Spec H`, or more generally of the affine
monoid of a bialgebra `H`, on `V(M)` by group automorphisms is linear: each point
`g : H →ₐ[R] A` acts on `V(M)(A) = M →ₗ[R] A` by an `A`-linear automorphism, and these form
homomorphisms to the `A`-linear automorphism groups, natural in `A`. This
is how a torus acts on a vector subgroup of a unipotent group in characteristic zero.

The proof follows the line through a point. For a point `f` and the polynomial algebra `A[X]`,
let a point `g` act on the point `X • f` of `V(M)` over `A[X]`. Naturality along the
substitution `X ↦ 2 X`, together with additivity, shows that every value of the result is a
polynomial `p` with `p (2 X) = 2 p (X)`, hence of the form `c X`
(`Polynomial.comp_C_two_mul_X_eq_C_two_mul_iff`); naturality along the evaluations `X ↦ a` then
gives `g • (a • f) = a • (g • f)`.

The rational hypothesis cannot be dropped: in characteristic `p > 0` the Frobenius
endomorphism of `𝔾ₐ` (`TauCeti.AdditiveGroup.frobeniusEnd`), `a ↦ a ^ p`, is a natural additive
endomorphism of the points of `𝔾ₐ` that is not linear.

## Main results

* `TauCeti.AdditiveGroup.map_smul_of_naturality`: a natural family of additive endomorphisms of
  the points of `V(M)`, parametrized by the points of `Spec H`, is linear over the value algebra.
* `TauCeti.AdditiveGroup.linearAutOfNaturality`: a natural action of an affine group, or monoid,
  on `V(M)` by group automorphisms, as homomorphisms to the `A`-linear automorphisms of
  `M →ₗ[R] A`.

## References

* J. S. Milne, *Algebraic Groups* (2017), the proof of Theorem 16.33, where a maximal torus acts
  linearly on a normal vector subgroup of a solvable group.
-/

public section

open Polynomial WithConv

namespace TauCeti

namespace AdditiveGroup

universe u v w x

section Naturality

variable {R : Type u} [CommRing R] [Algebra ℚ R] {H : Type v} [Semiring H] [Algebra R H]
variable {M : Type w} [AddCommMonoid M] [Module R M]

/-- **Natural additive endomorphisms of a vector group are linear in characteristic zero.** Over
a commutative `ℚ`-algebra `R`, let the points `g : H →ₐ[R] A` of `Spec H` act on the points
`M →ₗ[R] A` of the vector group `V(M)` by additive maps, naturally in the commutative
`R`-algebra `A`. Then each point acts `A`-linearly. -/
theorem map_smul_of_naturality
    (act : ∀ (A : Type x) [CommRing A] [Algebra R A], (H →ₐ[R] A) → (M →ₗ[R] A) →+ (M →ₗ[R] A))
    (act_comp : ∀ (A B : Type x) [CommRing A] [Algebra R A] [CommRing B] [Algebra R B]
      (φ : A →ₐ[R] B) (g : H →ₐ[R] A) (f : M →ₗ[R] A),
      φ.toLinearMap ∘ₗ act A g f = act B (φ.comp g) (φ.toLinearMap ∘ₗ f))
    {A : Type x} [CommRing A] [Algebra R A] (g : H →ₐ[R] A) (a : A) (f : M →ₗ[R] A) :
    act A g (a • f) = a • act A g f := by
  let _ : Algebra ℚ A := ((algebraMap R A).comp (algebraMap ℚ R)).toAlgebra
  have : HasUniqueDiv A := .of_module_rat A
  -- The constants, the doubling substitution and the evaluations of `A[X]`.
  let ι : A →ₐ[R] A[X] := IsScalarTower.toAlgHom R A A[X]
  let D : A[X] →ₐ[R] A[X] := (aeval (C 2 * X : A[X])).restrictScalars R
  let E (b : A) : A[X] →ₐ[R] A := (aeval b).restrictScalars R
  have hDι : D.comp ι = ι := AlgHom.ext fun c => by simp [D, ι]
  have hEι (b : A) : (E b).comp ι = AlgHom.id R A := AlgHom.ext fun c => by simp [E, ι]
  -- The point `X • f` over `A[X]`, the line through `f`, and the action of `g` on it.
  obtain ⟨y, hy⟩ : ∃ y : M →ₗ[R] A[X], (X : A[X]) • (ι.toLinearMap ∘ₗ f) = y := ⟨_, rfl⟩
  obtain ⟨P, hPy⟩ : ∃ P : M →ₗ[R] A[X], act A[X] (ι.comp g) y = P := ⟨_, rfl⟩
  have hDy : D.toLinearMap ∘ₗ y = y + y := by
    refine LinearMap.ext fun m => ?_
    simp only [← hy, LinearMap.coe_comp, Function.comp_apply, LinearMap.smul_apply,
      LinearMap.add_apply, AlgHom.toLinearMap_apply, smul_eq_mul, map_mul]
    simp only [D, ι, AlgHom.restrictScalars_apply, IsScalarTower.coe_toAlgHom', algebraMap_eq,
      aeval_C, aeval_X, C_ofNat]
    ring
  -- Doubling commutes with the action, so every value of `P` is linear in `X`.
  have hP (m : M) : P m = C ((P m).coeff 1) * X := by
    refine comp_C_two_mul_X_eq_C_two_mul_iff.mp ?_
    have h := congrArg (fun F : M →ₗ[R] A[X] => F m) (act_comp A[X] A[X] D (ι.comp g) y)
    rw [← AlgHom.comp_assoc, hDι, hDy, map_add, hPy] at h
    simp only [LinearMap.coe_comp, Function.comp_apply, AlgHom.toLinearMap_apply,
      LinearMap.add_apply] at h
    rw [comp_eq_aeval, ← AlgHom.restrictScalars_apply R, h, C_ofNat, two_mul]
  -- Evaluating at `X = b` recovers the action of `g` on `b • f`.
  have hact (b : A) (m : M) : act A g (b • f) m = (P m).coeff 1 * b := by
    have h := congrArg (fun F : M →ₗ[R] A => F m) (act_comp A[X] A (E b) (ι.comp g) y)
    have hEy : (E b).toLinearMap ∘ₗ y = b • f := by
      refine LinearMap.ext fun m => ?_
      simp only [← hy, LinearMap.coe_comp, Function.comp_apply, LinearMap.smul_apply,
        AlgHom.toLinearMap_apply, smul_eq_mul, map_mul]
      simp [E, ι, mul_comm b]
    rw [← AlgHom.comp_assoc, hEι, AlgHom.id_comp, hEy, hPy] at h
    simp only [LinearMap.coe_comp, Function.comp_apply, AlgHom.toLinearMap_apply] at h
    rw [← h, hP m]
    simp [E]
  ext m
  have h1 := hact 1 m
  rw [one_smul, mul_one] at h1
  rw [hact a m, LinearMap.smul_apply, h1, smul_eq_mul, mul_comm]

end Naturality

section Action

variable {R : Type u} [CommRing R] {H : Type v} [Semiring H] [Bialgebra R H]
variable {M : Type w} [AddCommMonoid M] [Module R M]
variable (act : ∀ (A : Type x) [CommRing A] [Algebra R A],
  WithConv (H →ₐ[R] A) →* MulAut (WithConv (SymmetricAlgebra R M →ₐ[R] A)))

/-- The action of a point `g` on the points of `V(M)`, read on their linear maps
`M →ₗ[R] A` (`TauCeti.AdditiveGroup.pointsMulEquiv`). -/
private noncomputable def paramAddAut (A : Type x) [CommRing A] [Algebra R A]
    (g : WithConv (H →ₐ[R] A)) : (M →ₗ[R] A) ≃+ (M →ₗ[R] A) :=
  AddEquiv.toMultiplicative.symm
    ((pointsMulEquiv (R := R) (M := M) (A := A)).symm.trans ((act A g).trans pointsMulEquiv))

private theorem paramAddAut_apply (A : Type x) [CommRing A] [Algebra R A]
    (g : WithConv (H →ₐ[R] A)) (P : WithConv (SymmetricAlgebra R M →ₐ[R] A)) :
    paramAddAut act A g (Multiplicative.toAdd (pointsMulEquiv P)) =
      Multiplicative.toAdd (pointsMulEquiv (act A g P)) := by
  -- Unfold the transport of `act A g` along `pointsMulEquiv` and cancel it.
  rw [paramAddAut, AddEquiv.toMultiplicative_symm_apply_apply, MulEquiv.trans_apply,
    MulEquiv.trans_apply, ofAdd_toAdd, MulEquiv.symm_apply_apply]

private theorem paramAddAut_mapValue
    (act_mapValue : ∀ (A B : Type x) [CommRing A] [Algebra R A] [CommRing B] [Algebra R B]
      (φ : A →ₐ[R] B) (g : WithConv (H →ₐ[R] A)) (P : WithConv (SymmetricAlgebra R M →ₐ[R] A)),
      AlgHom.mapValue φ (act A g P) = act B (AlgHom.mapValue φ g) (AlgHom.mapValue φ P))
    (A B : Type x) [CommRing A] [Algebra R A] [CommRing B] [Algebra R B] (φ : A →ₐ[R] B)
    (g : WithConv (H →ₐ[R] A)) (f : M →ₗ[R] A) :
    φ.toLinearMap ∘ₗ paramAddAut act A g f =
      paramAddAut act B (AlgHom.mapValue φ g) (φ.toLinearMap ∘ₗ f) := by
  obtain ⟨P, rfl⟩ : ∃ P, Multiplicative.toAdd (pointsMulEquiv P) = f :=
    ⟨pointsMulEquiv.symm (Multiplicative.ofAdd f), by simp⟩
  rw [paramAddAut_apply, ← toAdd_pointsMulEquiv_mapValue, ← toAdd_pointsMulEquiv_mapValue,
    paramAddAut_apply, act_mapValue]

/-- Over a `ℚ`-algebra, the action of a point on the linear maps of the points of `V(M)` is
linear over the value algebra. -/
private theorem paramAddAut_map_smul [Algebra ℚ R]
    (act_mapValue : ∀ (A B : Type x) [CommRing A] [Algebra R A] [CommRing B] [Algebra R B]
      (φ : A →ₐ[R] B) (g : WithConv (H →ₐ[R] A)) (P : WithConv (SymmetricAlgebra R M →ₐ[R] A)),
      AlgHom.mapValue φ (act A g P) = act B (AlgHom.mapValue φ g) (AlgHom.mapValue φ P))
    (A : Type x) [CommRing A] [Algebra R A] (g : WithConv (H →ₐ[R] A)) (a : A)
    (f : M →ₗ[R] A) :
    paramAddAut act A g (a • f) = a • paramAddAut act A g f := by
  have h := map_smul_of_naturality
    (fun A _ _ g => (paramAddAut act A (toConv g)).toAddMonoidHom)
    (fun A B _ _ _ _ φ g f => by
      simp only [AddEquiv.coe_toAddMonoidHom]
      rw [paramAddAut_mapValue act act_mapValue, AlgHom.mapValue_apply, ofConv_toConv])
    g.ofConv a f
  simpa only [AddEquiv.coe_toAddMonoidHom, toConv_ofConv] using h

/-- **Actions on vector groups in characteristic zero are linear.** Over a commutative
`ℚ`-algebra `R`, let the affine monoid `Spec H` of a bialgebra `H`, for instance an affine group,
act on the vector group `V(M)` by group automorphisms of the points, naturally in the commutative
`R`-algebra `A`. Then each point `g : H →ₐ[R] A` acts on the points `M →ₗ[R] A` of `V(M)` by an
`A`-linear automorphism, and this is a monoid homomorphism, a group homomorphism when `H` is a
Hopf algebra, to the `A`-linear automorphisms of `M →ₗ[R] A`
(`TauCeti.AdditiveGroup.linearAutOfNaturality_apply`), natural in `A`
(`TauCeti.AdditiveGroup.linearAutOfNaturality_mapValue`). -/
noncomputable def linearAutOfNaturality [Algebra ℚ R]
    (act_mapValue : ∀ (A B : Type x) [CommRing A] [Algebra R A] [CommRing B] [Algebra R B]
      (φ : A →ₐ[R] B) (g : WithConv (H →ₐ[R] A)) (P : WithConv (SymmetricAlgebra R M →ₐ[R] A)),
      AlgHom.mapValue φ (act A g P) = act B (AlgHom.mapValue φ g) (AlgHom.mapValue φ P))
    (A : Type x) [CommRing A] [Algebra R A] :
    WithConv (H →ₐ[R] A) →* ((M →ₗ[R] A) ≃ₗ[A] (M →ₗ[R] A)) where
  toFun g := (paramAddAut act A g).toLinearEquiv (paramAddAut_map_smul act act_mapValue A g)
  map_one' := LinearEquiv.ext fun f => by
    obtain ⟨P, rfl⟩ : ∃ P, Multiplicative.toAdd (pointsMulEquiv P) = f :=
      ⟨pointsMulEquiv.symm (Multiplicative.ofAdd f), by simp⟩
    simp only [AddEquiv.coe_toLinearEquiv, paramAddAut_apply, map_one, MulAut.one_apply,
      FunLike.coe_one_eq_id, id_eq]
  map_mul' g g' := LinearEquiv.ext fun f => by
    obtain ⟨P, rfl⟩ : ∃ P, Multiplicative.toAdd (pointsMulEquiv P) = f :=
      ⟨pointsMulEquiv.symm (Multiplicative.ofAdd f), by simp⟩
    simp only [AddEquiv.coe_toLinearEquiv, mul_apply_eq_comp, paramAddAut_apply, map_mul,
      MulAut.mul_apply]

variable [Algebra ℚ R]
  (act_mapValue : ∀ (A B : Type x) [CommRing A] [Algebra R A] [CommRing B] [Algebra R B]
    (φ : A →ₐ[R] B) (g : WithConv (H →ₐ[R] A)) (P : WithConv (SymmetricAlgebra R M →ₐ[R] A)),
    AlgHom.mapValue φ (act A g P) = act B (AlgHom.mapValue φ g) (AlgHom.mapValue φ P))

/-- The linear automorphism through which a point `g` acts sends the linear map `P ∘ ι` of a
point `P` of `V(M)` (`TauCeti.AdditiveGroup.toAdd_pointsMulEquiv`) to the linear map of
`g • P`. -/
@[simp]
theorem linearAutOfNaturality_apply (A : Type x) [CommRing A] [Algebra R A]
    (g : WithConv (H →ₐ[R] A)) (P : WithConv (SymmetricAlgebra R M →ₐ[R] A)) :
    linearAutOfNaturality act act_mapValue A g (P.ofConv.toLinearMap ∘ₗ SymmetricAlgebra.ι R M) =
      (act A g P).ofConv.toLinearMap ∘ₗ SymmetricAlgebra.ι R M :=
  paramAddAut_apply act A g P

/-- The linear automorphisms through which the points act are natural in the value algebra. -/
theorem linearAutOfNaturality_mapValue (A B : Type x) [CommRing A] [Algebra R A] [CommRing B]
    [Algebra R B] (φ : A →ₐ[R] B) (g : WithConv (H →ₐ[R] A)) (f : M →ₗ[R] A) :
    φ.toLinearMap ∘ₗ linearAutOfNaturality act act_mapValue A g f =
      linearAutOfNaturality act act_mapValue B (AlgHom.mapValue φ g) (φ.toLinearMap ∘ₗ f) :=
  paramAddAut_mapValue act act_mapValue A B φ g f

end Action

end AdditiveGroup

end TauCeti
