/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Center.Tangent
public import TauCeti.Algebra.AlgebraicGroup.Tangent.Lie.Adjoint.NilpotentCone

/-!
# The coadjoint nilpotent cone

Let `G = Spec H` be an affine group over a commutative ring `R` whose augmentation cotangent space
is finite projective, with Lie algebra `𝔤`, modelled as the dual of the cotangent space. The group
acts on `𝔤` by the adjoint representation (`Derivation.adjointComodule`) and on the dual `𝔤*` by
the coadjoint representation. The polynomial functions on `𝔤*` are the symmetric algebra
`Sym 𝔤`, and `G` acts on them through the comodule algebra
`TauCeti.ComoduleAlgebra.symmetricAlgebra` of the adjoint comodule. The invariant functions
`R[𝔤*]^G` (`TauCeti.coadjointInvariantPolynomials`) are the coordinate ring of the coadjoint
quotient `χ* : 𝔤* → 𝔤* // G`, and the **coadjoint nilpotent cone** is its scheme-theoretic zero
fibre `χ*⁻¹(0)`. Its ideal (`TauCeti.coadjointNilpotentConeIdeal`) is generated in `Sym 𝔤` by the
invariant functions vanishing at the origin, that is, it is the ideal
`Subalgebra.symmetricAlgebraHilbertIdeal` of the invariants. No reduction is taken, so a point
of `𝔤*` with values in a nonreduced algebra lies on the cone only when every invariant function
vanishing at the origin vanishes there.

The general properties of `Subalgebra.symmetricAlgebraHilbertIdeal` specialize: the cone contains
the origin, it is a cone, and it is stable under the coadjoint action. Invariant functions are
exactly those whose values at `A`-valued points of `𝔤*` are unchanged by the coadjoint action of
`A`-points of the group. Two criteria put a point on the cone. A covector scaled by `Tᵐ`, `m ≠ 0`,
under a point of the group with values in the Laurent polynomials `R[T;T⁻¹]`, such as a
cocharacter, lies on the cone. Every invariant is a Lie invariant for the action of `𝔤` on `Sym 𝔤`
by derivations extending `ad`; since a Lie-invariant linear function on `𝔤*` is a central element
of `𝔤`, a first-order point `ε • ψ` over the dual numbers lies on the cone as soon as the covector
`ψ` vanishes on the centre of `𝔤`.

Over a field `k`, a comodule isomorphism `𝔤 ≅ 𝔤*` between the adjoint and the coadjoint
representations, such as the one given by an invariant nondegenerate bilinear form, carries the
ideal of the coadjoint cone onto the ideal `TauCeti.nilpotentConeIdeal` of the adjoint cone. This
holds for every such isomorphism, so the two cones correspond as closed subschemes independently
of the choice. For a commutative group the coadjoint action is trivial and the cone is the
origin: its ideal is the augmentation ideal. This covers the trivial group.

## Main declarations

* `TauCeti.coadjointInvariantPolynomials`: the invariant polynomial functions `R[𝔤*]^G`, with
  the point criterion
  `TauCeti.mem_coadjointInvariantPolynomials_iff_lift_liftBaseChange_endOfPoint`.
* `TauCeti.coadjointNilpotentConeIdeal`: the ideal of the zero fibre of the coadjoint quotient,
  with its universal property `TauCeti.coadjointNilpotentConeIdeal_le_iff`.
* `TauCeti.coadjointNilpotentConeIdeal_le_ker_algebraMapInv`,
  `TauCeti.coadjointNilpotentConeIdeal_isHomogeneous` and
  `TauCeti.symmetricAlgebraCoact_mem_map_includeLeft_coadjointNilpotentConeIdeal`: the cone
  contains the origin, is stable under scaling, and is stable under the coadjoint action.
* `TauCeti.coadjointNilpotentConeIdeal_le_ker_lift_of_endOfPoint`: a covector scaled by a
  cocharacter lies on the cone.
* `TauCeti.coadjointInvariantPolynomials_le_lieInvariants`: invariant functions are Lie
  invariants.
* `TauCeti.coadjointNilpotentConeIdeal_le_ker_lift_smulRight`: the first-order point `ε • ψ`
  lies on the cone when `ψ` vanishes on the centre of `𝔤`.
* `TauCeti.map_coadjointNilpotentConeIdeal`: a comodule isomorphism `𝔤 ≅ 𝔤*` carries the ideal of
  the coadjoint cone onto the ideal of the adjoint cone.
* `TauCeti.coadjointNilpotentConeIdeal_eq_ker_algebraMapInv_of_isCocomm` and
  `TauCeti.coadjointNilpotentConeIdeal_le_ker_lift_iff_of_isCocomm`: for a commutative group the
  cone is the origin, even on points with values in a nonreduced algebra; in particular for the
  trivial group (`TauCeti.coadjointNilpotentConeIdeal_self_eq_ker_algebraMapInv`).

## References

* L. Fargues and P. Scholze, *Geometrization of the local Langlands correspondence*, proof of
  Proposition VIII.2.11.
-/

public section

open scoped TensorProduct LaurentPolynomial

namespace TauCeti

universe u v

attribute [local instance] Derivation.adjointComodule ComoduleAlgebra.symmetricAlgebra

section Basic

variable (R : Type u) [CommRing R] (H : Type v) [CommRing H] [HopfAlgebra R H]
  [Module.Finite R (Bialgebra.CotangentSpace R H)]
  [Module.Projective R (Bialgebra.CotangentSpace R H)]

local notation "𝔤" => Module.Dual R (Bialgebra.CotangentSpace R H)

/-- The polynomial functions on the dual `𝔤*` of the Lie algebra of `Spec H` which are invariant
under the coadjoint action: the coinvariants of the symmetric algebra `Sym 𝔤` of the adjoint
comodule, and the coordinate ring of the coadjoint quotient `𝔤* // G`. -/
noncomputable def coadjointInvariantPolynomials : Subalgebra R (SymmetricAlgebra R 𝔤) :=
  ComoduleAlgebra.coinvariants R H (SymmetricAlgebra R 𝔤)

variable {R H}

/-- A polynomial function on `𝔤*` is invariant when its coaction, the algebra map extending the
adjoint coaction on `𝔤`, is trivial. -/
@[simp]
theorem mem_coadjointInvariantPolynomials {p : SymmetricAlgebra R 𝔤} :
    p ∈ coadjointInvariantPolynomials R H ↔
      Comodule.symmetricAlgebraCoact R H 𝔤 p = p ⊗ₜ[R] (1 : H) := by
  rw [coadjointInvariantPolynomials, ComoduleAlgebra.mem_coinvariants,
    ComoduleAlgebra.symmetricAlgebra_coact, AlgHom.toLinearMap_apply]

/-- The homogeneous components of an invariant polynomial function on `𝔤*` are invariant. -/
theorem decompose_mem_coadjointInvariantPolynomials {p : SymmetricAlgebra R 𝔤}
    (hp : p ∈ coadjointInvariantPolynomials R H) (n : ℕ) :
    (DirectSum.decompose (SymmetricAlgebra.homogeneousSubmodule R 𝔤) p n :
      SymmetricAlgebra R 𝔤) ∈ coadjointInvariantPolynomials R H :=
  ComoduleAlgebra.decompose_mem_coinvariants_symmetricAlgebra hp n

/-- **Invariant functions on `𝔤*` are invariant under all points.** The value of an invariant
polynomial function at an `A`-valued point `ψ` of `𝔤*` does not change when `ψ` is translated by
the coadjoint action of an `A`-point `g` of `Spec H`. -/
theorem lift_liftBaseChange_endOfPoint_of_mem_coadjointInvariantPolynomials {A : Type*}
    [CommSemiring A] [Algebra R A] {p : SymmetricAlgebra R 𝔤}
    (hp : p ∈ coadjointInvariantPolynomials R H) (g : H →ₐ[R] A) (ψ : 𝔤 →ₗ[R] A) :
    SymmetricAlgebra.lift ((LinearMap.liftBaseChange A ψ).restrictScalars R ∘ₗ
        (Comodule.endOfPoint 𝔤 g).restrictScalars R ∘ₗ TensorProduct.mk R A 𝔤 1) p =
      SymmetricAlgebra.lift ψ p :=
  ComoduleAlgebra.lift_liftBaseChange_endOfPoint_of_mem_coinvariants hp g ψ

/-- **Invariant functions on `𝔤*` are the functions invariant under all points.** A polynomial
function on `𝔤*` is invariant exactly when its value at every `A`-valued point is unchanged by the
coadjoint action of every `A`-point of `Spec H`. -/
theorem mem_coadjointInvariantPolynomials_iff_lift_liftBaseChange_endOfPoint
    {p : SymmetricAlgebra R 𝔤} :
    p ∈ coadjointInvariantPolynomials R H ↔
      ∀ (A : Type (max u v)) [CommRing A] [Algebra R A] (g : H →ₐ[R] A) (ψ : 𝔤 →ₗ[R] A),
        SymmetricAlgebra.lift ((LinearMap.liftBaseChange A ψ).restrictScalars R ∘ₗ
          (Comodule.endOfPoint 𝔤 g).restrictScalars R ∘ₗ TensorProduct.mk R A 𝔤 1) p =
          SymmetricAlgebra.lift ψ p :=
  ComoduleAlgebra.mem_coinvariants_symmetricAlgebra_iff_lift_liftBaseChange_endOfPoint

variable (R H) in
/-- **The ideal of the coadjoint nilpotent cone.** The ideal of `Sym 𝔤 = R[𝔤*]` generated by the
invariant polynomial functions on `𝔤*` vanishing at the origin: the ideal of the scheme-theoretic
zero fibre of the coadjoint quotient map `𝔤* → 𝔤* // G`. -/
noncomputable def coadjointNilpotentConeIdeal : Ideal (SymmetricAlgebra R 𝔤) :=
  (coadjointInvariantPolynomials R H).symmetricAlgebraHilbertIdeal

/-- An invariant polynomial function on `𝔤*` vanishing at the origin lies in the ideal of the
coadjoint nilpotent cone. -/
theorem mem_coadjointNilpotentConeIdeal_of_mem_coadjointInvariantPolynomials
    {p : SymmetricAlgebra R 𝔤} (hp : p ∈ coadjointInvariantPolynomials R H)
    (hp₀ : SymmetricAlgebra.algebraMapInv p = 0) : p ∈ coadjointNilpotentConeIdeal R H :=
  Subalgebra.mem_symmetricAlgebraHilbertIdeal_of_mem hp hp₀

/-- **The universal property of the ideal of the coadjoint nilpotent cone.** An ideal contains it
exactly when it contains every invariant polynomial function on `𝔤*` vanishing at the origin. In
particular a point of `𝔤*` with values in any ring, that is a ring homomorphism out of `Sym 𝔤`,
lies on the cone exactly when it kills these invariants. -/
theorem coadjointNilpotentConeIdeal_le_iff {I : Ideal (SymmetricAlgebra R 𝔤)} :
    coadjointNilpotentConeIdeal R H ≤ I ↔
      ∀ p ∈ coadjointInvariantPolynomials R H, SymmetricAlgebra.algebraMapInv p = 0 → p ∈ I :=
  Subalgebra.symmetricAlgebraHilbertIdeal_le_iff

/-- The origin lies on the coadjoint nilpotent cone: its ideal is contained in the augmentation
ideal. -/
theorem coadjointNilpotentConeIdeal_le_ker_algebraMapInv :
    coadjointNilpotentConeIdeal R H ≤
      RingHom.ker (SymmetricAlgebra.algebraMapInv : SymmetricAlgebra R 𝔤 →ₐ[R] R) :=
  coadjointNilpotentConeIdeal_le_iff.mpr fun _ _ hp₀ ↦ hp₀

/-- **The coadjoint nilpotent cone is a cone.** Its ideal is homogeneous: it is generated by the
homogeneous components of positive degree of the invariant polynomial functions, which are again
invariant. -/
theorem coadjointNilpotentConeIdeal_isHomogeneous :
    (coadjointNilpotentConeIdeal R H).IsHomogeneous
      (SymmetricAlgebra.homogeneousSubmodule R 𝔤) :=
  Subalgebra.isHomogeneous_symmetricAlgebraHilbertIdeal fun n _ hp ↦
    decompose_mem_coadjointInvariantPolynomials hp n

/-- **The coadjoint nilpotent cone is stable under the coadjoint action.** The coaction carries
its ideal into the ideal it generates in `Sym 𝔤 ⊗ H`, since it is generated by invariants. -/
theorem symmetricAlgebraCoact_mem_map_includeLeft_coadjointNilpotentConeIdeal
    {p : SymmetricAlgebra R 𝔤} (hp : p ∈ coadjointNilpotentConeIdeal R H) :
    Comodule.symmetricAlgebraCoact R H 𝔤 p ∈
      (coadjointNilpotentConeIdeal R H).map (Algebra.TensorProduct.includeLeft (R := R)
        (S := R) (A := SymmetricAlgebra R 𝔤) (B := H)) := by
  have h := ComoduleAlgebra.coact_mem_map_includeLeft_symmetricAlgebraHilbertIdeal hp
  rwa [ComoduleAlgebra.symmetricAlgebra_coact, AlgHom.toLinearMap_apply] at h

/-- **Points scaled by a cocharacter lie on the coadjoint nilpotent cone.** Let `ψ` be an
`R`-valued point of `𝔤*`. Suppose some point `g` of `Spec H` with values in the Laurent polynomials
`R[T;T⁻¹]`, such as a cocharacter `𝔾ₘ → Spec H`, scales `ψ` by `Tᵐ` for some `m ≠ 0`. Then `ψ` lies
on the coadjoint nilpotent cone: a homogeneous invariant of degree `n` takes at `ψ` a value `c`
with `Tⁿᵐ c = c`, which forces `c = 0` when `n > 0`. -/
theorem coadjointNilpotentConeIdeal_le_ker_lift_of_endOfPoint {ψ : Module.Dual R 𝔤}
    (g : H →ₐ[R] R[T;T⁻¹]) {m : ℤ} (hm : m ≠ 0)
    (hg : ∀ x : 𝔤, LinearMap.liftBaseChange R[T;T⁻¹] ((Algebra.linearMap R R[T;T⁻¹]) ∘ₗ ψ)
        (Comodule.endOfPoint 𝔤 g (1 ⊗ₜ[R] x)) =
      LaurentPolynomial.T m * algebraMap R R[T;T⁻¹] (ψ x)) :
    coadjointNilpotentConeIdeal R H ≤ RingHom.ker (SymmetricAlgebra.lift ψ) := by
  classical
  refine coadjointNilpotentConeIdeal_le_iff.mpr fun p hp hp₀ ↦ ?_
  rw [RingHom.mem_ker, ← DirectSum.sum_support_decompose
    (SymmetricAlgebra.homogeneousSubmodule R 𝔤) p, map_sum]
  refine Finset.sum_eq_zero fun n _ ↦ ?_
  have hq := (DirectSum.decompose (SymmetricAlgebra.homogeneousSubmodule R 𝔤) p n).property
  have hφ : SymmetricAlgebra.lift ((Algebra.linearMap R R[T;T⁻¹]) ∘ₗ ψ) =
      (Algebra.ofId R R[T;T⁻¹]).comp (SymmetricAlgebra.lift ψ) :=
    SymmetricAlgebra.algHom_ext (LinearMap.ext fun x ↦ by simp)
  -- The translate of `ψ` by `g` is `Tᵐ ψ`, so invariance of the component `q` of degree `n` gives
  -- `Tⁿᵐ q(ψ) = q(ψ)`.
  have hinv := lift_liftBaseChange_endOfPoint_of_mem_coadjointInvariantPolynomials
    (decompose_mem_coadjointInvariantPolynomials hp n) g ((Algebra.linearMap R R[T;T⁻¹]) ∘ₗ ψ)
  rw [AlgHom.apply_eq_pow_mul_of_forall_ι_eq
    (SymmetricAlgebra.lift ((Algebra.linearMap R R[T;T⁻¹]) ∘ₗ ψ)) _ (LaurentPolynomial.T m)
    (fun x ↦ by
      simp only [SymmetricAlgebra.lift_ι_apply, LinearMap.comp_apply,
        LinearMap.restrictScalars_apply, TensorProduct.mk_apply]
      exact hg x) hq, hφ, AlgHom.comp_apply, Algebra.ofId_apply,
    LaurentPolynomial.T_pow, ← LaurentPolynomial.C_eq_algebraMap, mul_comm] at hinv
  rcases n with _ | n
  · -- The component of degree zero is the value at the origin.
    rw [← SymmetricAlgebra.mem_irrelevant_iff_algebraMapInv_eq_zero,
      HomogeneousIdeal.mem_irrelevant_iff, GradedRing.proj_apply] at hp₀
    rw [hp₀, map_zero]
  · -- Compare the coefficients of `Tⁿᵐ`, with `nm ≠ 0`.
    rw [← LaurentPolynomial.single_eq_C_mul_T] at hinv
    have h := congrArg (fun f ↦ f.coeff (((n + 1 : ℕ) : ℤ) * m)) hinv
    simp only [AddMonoidAlgebra.coeff_single, Finsupp.single_eq_same,
      LaurentPolynomial.C_apply] at h
    simpa [hm, Nat.cast_add_one_ne_zero] using h

end Basic

section Lie

variable {R H : Type u} [CommRing R] [CommRing H] [HopfAlgebra R H]
  [Module.Finite R (Bialgebra.CotangentSpace R H)]
  [Module.Projective R (Bialgebra.CotangentSpace R H)]

local notation "𝔤" => Module.Dual R (Bialgebra.CotangentSpace R H)

/-- **Invariant functions on `𝔤*` are Lie invariants.** An invariant polynomial function on `𝔤*` is
killed by the action of `𝔤` on `Sym 𝔤` by the derivations extending `ad`, since this is the
differentiated coadjoint action. No connectedness or characteristic assumption is needed. -/
theorem coadjointInvariantPolynomials_le_lieInvariants :
    coadjointInvariantPolynomials R H ≤ SymmetricAlgebra.lieInvariants R 𝔤 𝔤 := by
  intro p hp
  rw [SymmetricAlgebra.mem_lieInvariants]
  intro x
  have h := Comodule.differential_eq_zero_of_coact_eq_tmul_one
    (ComoduleAlgebra.mem_coinvariants.mp hp) (Derivation.cotangentDualLieEquiv (R := R) (H := H) x)
  have hend : Comodule.differential (R := R) (H := H) (M := 𝔤)
      (Derivation.cotangentDualLieEquiv (R := R) (H := H) x) = LieModule.toEnd R 𝔤 𝔤 x := by
    ext y
    rw [Derivation.differential_adjointComodule, LieEquiv.symm_apply_apply,
      LieModule.toEnd_apply_apply]
  rw [ComoduleAlgebra.differential_symmetricAlgebra, hend] at h
  rwa [SymmetricAlgebra.lieModuleDerivation_apply]

/-- **First-order points of the coadjoint nilpotent cone.** Let `ψ` be a covector vanishing on the
centre of `𝔤` and `e` an element of square zero in an `R`-algebra `A`, such as `ε` in the dual
numbers. Then the point `e • ψ` of `𝔤*` with values in `A` lies on the coadjoint nilpotent cone.
Indeed an invariant function vanishing at the origin has first-order part an invariant linear
function on `𝔤*`, that is a central element of `𝔤`, and its higher-order parts are killed by
`e ^ 2 = 0`. -/
theorem coadjointNilpotentConeIdeal_le_ker_lift_smulRight {A : Type*} [CommSemiring A]
    [Algebra R A]
    {e : A} (he : e * e = 0) {ψ : Module.Dual R 𝔤}
    (hψ : ∀ z : 𝔤, (∀ x : 𝔤, ⁅x, z⁆ = 0) → ψ z = 0) :
    coadjointNilpotentConeIdeal R H ≤ RingHom.ker (SymmetricAlgebra.lift (ψ.smulRight e)) := by
  classical
  refine coadjointNilpotentConeIdeal_le_iff.mpr fun p hp hp₀ ↦ ?_
  rw [RingHom.mem_ker, ← DirectSum.sum_support_decompose
    (SymmetricAlgebra.homogeneousSubmodule R 𝔤) p, map_sum]
  refine Finset.sum_eq_zero fun n _ ↦ ?_
  have hq := (DirectSum.decompose (SymmetricAlgebra.homogeneousSubmodule R 𝔤) p n).property
  -- On a homogeneous element of degree `n`, the point `e • ψ` takes `e ^ n` times the value of
  -- `ψ`.
  rw [AlgHom.apply_eq_pow_mul_of_forall_ι_eq
    (SymmetricAlgebra.lift ((Algebra.linearMap R A).comp ψ))
    (SymmetricAlgebra.lift (ψ.smulRight e)) e
    (fun m ↦ by simp [Algebra.smul_def, mul_comm]) hq]
  rcases n with _ | _ | n
  · -- The component of degree zero is the value at the origin.
    rw [← SymmetricAlgebra.mem_irrelevant_iff_algebraMapInv_eq_zero,
      HomogeneousIdeal.mem_irrelevant_iff, GradedRing.proj_apply] at hp₀
    rw [hp₀, map_zero, mul_zero]
  · -- The component of degree one is an invariant linear function, a central element of `𝔤`.
    rw [zero_add] at hq ⊢
    have hz := SymmetricAlgebra.ι_homogeneousSubmoduleOneEquiv_apply R 𝔤 ⟨_, hq⟩
    set z := SymmetricAlgebra.homogeneousSubmoduleOneEquiv R 𝔤 ⟨_, hq⟩
    have hinv := SymmetricAlgebra.decompose_mem_lieInvariants
      (coadjointInvariantPolynomials_le_lieInvariants hp) 1
    rw [← hz, SymmetricAlgebra.ι_mem_lieInvariants_iff] at hinv
    rw [← hz, SymmetricAlgebra.lift_ι_apply, LinearMap.comp_apply, hψ z hinv, map_zero,
      mul_zero]
  · rw [show e ^ (n + 1 + 1) = 0 by rw [pow_succ, pow_succ, mul_assoc, he, mul_zero], zero_mul]

end Lie

section Field

variable {k : Type u} [Field k] {H : Type u} [CommRing H] [HopfAlgebra k H]
  [Module.Finite k (Bialgebra.CotangentSpace k H)]

local notation "𝔤" => Module.Dual k (Bialgebra.CotangentSpace k H)

/-- The invariant polynomial functions on the Lie algebra are the coinvariants of the symmetric
algebra of the contragredient of the adjoint comodule. -/
private theorem mem_adjointInvariantPolynomials_iff_mem_coinvariants
    {p : SymmetricAlgebra k (Module.Dual k 𝔤)} :
    letI := Comodule.dual k H 𝔤
    p ∈ adjointInvariantPolynomials k H ↔
      p ∈ ComoduleAlgebra.coinvariants k H (SymmetricAlgebra k (Module.Dual k 𝔤)) := by
  let := Comodule.dual k H 𝔤
  -- Both coactions are algebra maps extending the contragredient coaction on generators.
  have h : (letI := adjointPolynomialComoduleAlgebra k H
      ComoduleAlgebra.coactAlgHom k H (SymmetricAlgebra k (Module.Dual k 𝔤))) =
      Comodule.symmetricAlgebraCoact k H (Module.Dual k 𝔤) := by
    let := adjointPolynomialComoduleAlgebra k H
    refine SymmetricAlgebra.algHom_ext (LinearMap.ext fun φ ↦ ?_)
    simp only [LinearMap.coe_comp, LinearMap.coe_ofClass, Function.comp_apply,
      ComoduleAlgebra.coactAlgHom_apply, adjointPolynomialComoduleAlgebra_coact_ι,
      Comodule.symmetricAlgebraCoact_ι, Comodule.dual_coact]
  have hp : (letI := adjointPolynomialComoduleAlgebra k H
      Comodule.coact (R := k) (C := H) p) = Comodule.symmetricAlgebraCoact k H _ p := by
    let := adjointPolynomialComoduleAlgebra k H
    rw [← ComoduleAlgebra.coactAlgHom_apply, h]
  rw [mem_adjointInvariantPolynomials, hp, ComoduleAlgebra.mem_coinvariants,
    ComoduleAlgebra.symmetricAlgebra_coact, AlgHom.toLinearMap_apply]

/-- The ideal of the adjoint nilpotent cone is the ideal generated by the coinvariants of the
symmetric algebra of the contragredient of the adjoint comodule vanishing at the origin. -/
private theorem nilpotentConeIdeal_eq_symmetricAlgebraHilbertIdeal :
    letI := Comodule.dual k H 𝔤
    nilpotentConeIdeal k H = (ComoduleAlgebra.coinvariants k H
      (SymmetricAlgebra k (Module.Dual k 𝔤))).symmetricAlgebraHilbertIdeal := by
  let := Comodule.dual k H 𝔤
  refine le_antisymm (nilpotentConeIdeal_le_iff.mpr fun p hp hp₀ ↦ ?_)
    (Subalgebra.symmetricAlgebraHilbertIdeal_le_iff.mpr fun p hp hp₀ ↦ ?_)
  · exact Subalgebra.mem_symmetricAlgebraHilbertIdeal_of_mem
      (mem_adjointInvariantPolynomials_iff_mem_coinvariants.mp hp) hp₀
  · exact mem_nilpotentConeIdeal_of_mem_adjointInvariantPolynomials
      (mem_adjointInvariantPolynomials_iff_mem_coinvariants.mpr hp) hp₀

attribute [local instance] Comodule.dual

/-- **The adjoint and coadjoint nilpotent cones correspond.** Let `f : 𝔤 → 𝔤*` be a comodule
morphism from the adjoint to the coadjoint representation with a comodule section, in particular a
comodule isomorphism, such as the one given by an invariant nondegenerate bilinear form on `𝔤`.
Then the induced isomorphism `Sym 𝔤 → Sym 𝔤*` of polynomial functions on `𝔤*` and on `𝔤` carries
the ideal of the coadjoint nilpotent cone onto the ideal of the adjoint nilpotent cone. So `f`
identifies the two cones as closed subschemes, whichever such `f` is chosen. -/
theorem map_coadjointNilpotentConeIdeal (f : Comodule.Hom k H 𝔤 (Module.Dual k 𝔤))
    (g : Comodule.Hom k H (Module.Dual k 𝔤) 𝔤) (hfg : Function.LeftInverse f g) :
    (coadjointNilpotentConeIdeal k H).map (SymmetricAlgebra.map k f.toLinearMap) =
      nilpotentConeIdeal k H := by
  rw [nilpotentConeIdeal_eq_symmetricAlgebraHilbertIdeal]
  exact f.map_symmetricAlgebraHilbertIdeal g hfg

end Field

section Cocomm

variable {k : Type u} [Field k]

/-- **The coadjoint nilpotent cone of a commutative group is the origin.** If the coordinate Hopf
algebra is cocommutative, the coadjoint action is trivial, every polynomial function on `𝔤*` is
invariant, and the ideal of the cone is the augmentation ideal. -/
theorem coadjointNilpotentConeIdeal_eq_ker_algebraMapInv_of_isCocomm
    (H : CommHopfAlgCat.{u} k) [Module.Finite k (Bialgebra.CotangentSpace k H)]
    [Coalgebra.IsCocomm k H] :
    coadjointNilpotentConeIdeal k H = RingHom.ker (SymmetricAlgebra.algebraMapInv :
      SymmetricAlgebra k (Module.Dual k (Bialgebra.CotangentSpace k H)) →ₐ[k] k) :=
  ComoduleAlgebra.symmetricAlgebraHilbertIdeal_coinvariants_eq_ker_algebraMapInv
    (CommHopfAlgCat.coact_adjointComodule_eq_tmul_one_of_isCocomm H)

/-- **The points of the coadjoint nilpotent cone of a commutative group.** If the coordinate Hopf
algebra is cocommutative, a point of `𝔤*` with values in any `k`-algebra `A`, that is a linear
map `ψ : 𝔤 → A`, lies on the coadjoint nilpotent cone only when it is zero. This holds also over a
nonreduced `A`, where a nonzero `ψ` can vanish at every geometric point. -/
theorem coadjointNilpotentConeIdeal_le_ker_lift_iff_of_isCocomm
    (H : CommHopfAlgCat.{u} k) [Module.Finite k (Bialgebra.CotangentSpace k H)]
    [Coalgebra.IsCocomm k H] {A : Type*} [CommSemiring A] [Algebra k A]
    {ψ : Module.Dual k (Bialgebra.CotangentSpace k H) →ₗ[k] A} :
    coadjointNilpotentConeIdeal k H ≤ RingHom.ker (SymmetricAlgebra.lift ψ) ↔ ψ = 0 := by
  rw [coadjointNilpotentConeIdeal_eq_ker_algebraMapInv_of_isCocomm]
  refine ⟨fun h ↦ LinearMap.ext fun x ↦ ?_, ?_⟩
  · have hx := h (SymmetricAlgebra.algebraMapInv_ι x)
    rwa [RingHom.mem_ker, SymmetricAlgebra.lift_ι_apply] at hx
  · rintro rfl p hp
    have h0 : SymmetricAlgebra.lift (0 : Module.Dual k (Bialgebra.CotangentSpace k H) →ₗ[k] A) =
        (Algebra.ofId k A).comp SymmetricAlgebra.algebraMapInv :=
      SymmetricAlgebra.algHom_ext <| LinearMap.ext fun x ↦ by
        simp [SymmetricAlgebra.algebraMapInv_ι]
    rw [RingHom.mem_ker, h0, AlgHom.comp_apply, RingHom.mem_ker.mp hp, map_zero]

variable (k) in
/-- **The coadjoint nilpotent cone of the trivial group is a point.** For the trivial group
`Spec k`, the ideal of the coadjoint nilpotent cone is the augmentation ideal. -/
theorem coadjointNilpotentConeIdeal_self_eq_ker_algebraMapInv :
    coadjointNilpotentConeIdeal k k = RingHom.ker (SymmetricAlgebra.algebraMapInv :
      SymmetricAlgebra k (Module.Dual k (Bialgebra.CotangentSpace k k)) →ₐ[k] k) :=
  coadjointNilpotentConeIdeal_eq_ker_algebraMapInv_of_isCocomm (CommHopfAlgCat.of k k)

end Cocomm

end TauCeti
