/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.LinearAlgebra.TensorProduct.Basis
public import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import TauCeti.RingTheory.HahnSeries.Multiplication

-- Proof-only: integer support bounds and independent families.
import Mathlib.Data.Int.Interval
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition

/-!
# Scalar extension and module-valued Hahn series

The canonical map `R⟦Γ⟧ ⊗[R] V → HahnModule Γ R V` sends `f ⊗ v` to the series with
coefficients `f.coeff g • v`, or equivalently to `f` times the constant series `v`.
For a finite free coefficient module this is an isomorphism over `R⟦Γ⟧`: expansion in any
finite basis of `V` writes a module-valued series as a finite sum of scalar series times
constant basis vectors. The map itself is independent of that basis.

In particular, for a finite-dimensional vector space `V` over a field `K`, this identifies
`K((t)) ⊗[K] V` with `V((t))` on Mathlib's `HahnModule ℤ K V` carrier, with its convolution
action of scalar Laurent series. This supplies the scalar-extension interpretation of
module-valued Laurent series used in residue duality.

In arbitrary dimension the comparison is injective for free coefficients. Over a field its
image consists exactly of series whose coefficients lie in a single finite-dimensional
subspace. For integer exponents and free coefficients over a nontrivial commutative ring, it
is surjective if and only if the coefficient module is finitely generated (equivalently,
finite-dimensional over a field): a series with an independent sequence of coefficients cannot
be a finite sum of scalar series times vectors. This distinguishes tensor currents from their
coefficientwise completion.

## References

* E. Frenkel, *Langlands Correspondence for Loop Groups*, §1.3.1, for tensor currents and
  the finite-dimensional comparison.
-/

public section

noncomputable section

open TensorProduct HahnSeries

namespace HahnModule

variable {Γ R V : Type*} [AddCommMonoid Γ] [PartialOrder Γ]
  [IsOrderedCancelAddMonoid Γ]

variable [CommSemiring R] [AddCommMonoid V] [Module R V]

variable (R Γ V) in
/-- The canonical scalar-extension map to module-valued Hahn series, sending `f ⊗ v` to
`f` times the constant series `v`. -/
def tensorProductToHahnModule :
    HahnSeries Γ R ⊗[R] V →ₗ[HahnSeries Γ R] HahnModule Γ R V :=
  TensorProduct.AlgebraTensorModule.lift
    { toFun := fun f ↦
        { toFun := fun v ↦ f • of R (single 0 v)
          map_add' := fun v w ↦ by rw [single_add, of_add, smul_add]
          map_smul' := fun r v ↦ by
            apply HahnModule.ext
            funext g
            simp only [coeff_smul_single_zero, RingHom.id_apply, of_symm_smul',
              HahnSeries.coeff_smul]
            exact (smul_comm r (f.coeff g) v).symm }
      map_add' := fun f h ↦
        LinearMap.ext fun v ↦ _root_.add_smul f h (of R (single 0 v))
      map_smul' := fun f h ↦ LinearMap.ext fun v ↦ mul_smul f h (of R (single 0 v)) }

/-- The scalar-extension map on a pure tensor is multiplication by a constant series. -/
@[simp]
theorem tensorProductToHahnModule_tmul (f : HahnSeries Γ R) (v : V) :
    tensorProductToHahnModule Γ R V (f ⊗ₜ[R] v) = f • of R (single 0 v) :=
  (rfl)

/-- Scalar extension commutes with linear maps on the coefficient module, coefficient by
coefficient. No finiteness assumption is needed for this naturality identity. -/
theorem coeff_tensorProductToHahnModule_map {W : Type*} [AddCommMonoid W] [Module R W]
    (ℓ : V →ₗ[R] W) (z : HahnSeries Γ R ⊗[R] V) (g : Γ) :
    ((of R).symm (tensorProductToHahnModule Γ R W
      (TensorProduct.map (.id : HahnSeries Γ R →ₗ[R] _) ℓ z))).coeff g =
      ℓ (((of R).symm (tensorProductToHahnModule Γ R V z)).coeff g) := by
  induction z using TensorProduct.inductionOn with
  | tmul f v => simp
  | add z w hz hw => simp [hz, hw]

/-- A finite basis expands a module-valued Hahn series into scalar coordinate series times
constant basis vectors. -/
theorem sum_map_coord_smul_single {ι : Type*} [Fintype ι] (b : Module.Basis ι R V)
    (x : HahnModule Γ R V) :
    ∑ i, ((of R).symm x).map (b.coord i) • of R (single 0 (b i)) = x := by
  apply HahnModule.ext
  funext g
  -- Use the bundled linear equivalence so `map_sum` distributes the inverse of `of`.
  rw [← ofLinearEquiv_symm_apply]
  simp only [map_sum, ofLinearEquiv_symm_apply, coeff_sum, coeff_smul_single_zero, map_coeff,
    Module.Basis.coord_apply]
  exact b.sum_repr _

/-- The scalar-extension map is bijective whenever the coefficient module has a finite basis. -/
theorem tensorProductToHahnModule_bijective_of_basis {ι : Type*} [Finite ι]
    (b : Module.Basis ι R V) : Function.Bijective (tensorProductToHahnModule Γ R V) := by
  classical
  let := Fintype.ofFinite ι
  let inv : HahnModule Γ R V →+ HahnSeries Γ R ⊗[R] V :=
    ∑ i, { toFun := fun x ↦ ((of R).symm x).map (b.coord i) ⊗ₜ[R] b i
           map_zero' := by
             rw [of_symm_zero, show (0 : HahnSeries Γ V).map (b.coord i) = 0 by ext; simp,
               zero_tmul]
           map_add' := fun x y ↦ by
             rw [of_symm_add, ← add_tmul]
             congr 1
             exact HahnSeries.map_add (b.coord i).toAddMonoidHom }
  have right : Function.RightInverse inv (tensorProductToHahnModule Γ R V) := by
    intro x
    simp only [inv, AddMonoidHom.finsetSum_apply, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
      map_sum, tensorProductToHahnModule_tmul]
    exact sum_map_coord_smul_single b x
  have left : Function.LeftInverse inv (tensorProductToHahnModule Γ R V) := by
    intro z
    induction z using TensorProduct.inductionOn with
    | tmul f v =>
      have hc (i : ι) :
          ((of R).symm (tensorProductToHahnModule Γ R V (f ⊗ₜ[R] v))).map (b.coord i) =
            b.repr v i • f := by
        ext g
        simp [smul_eq_mul, mul_comm]
      simp only [inv, AddMonoidHom.finsetSum_apply, AddMonoidHom.coe_mk, ZeroHom.coe_mk, hc,
        smul_tmul, ← tmul_sum, b.sum_repr]
    | add z w hz hw => simp only [map_add, hz, hw]
  exact ⟨left.injective, right.surjective⟩

variable (R Γ V) in
/-- Finite free coefficient modules commute with scalar extension to Hahn series. In
particular this is `K((t)) ⊗[K] V ≃ V((t))` for finite-dimensional `V`. -/
def tensorProductEquiv [Module.Free R V] [Module.Finite R V] :
    HahnSeries Γ R ⊗[R] V ≃ₗ[HahnSeries Γ R] HahnModule Γ R V :=
  LinearEquiv.ofBijective (tensorProductToHahnModule Γ R V)
    (tensorProductToHahnModule_bijective_of_basis (Module.Free.chooseBasis R V))

/-- The equivalence has the canonical scalar-extension map as its forward map. -/
@[simp]
theorem tensorProductEquiv_apply [Module.Free R V] [Module.Finite R V]
    (z : HahnSeries Γ R ⊗[R] V) :
    tensorProductEquiv Γ R V z = tensorProductToHahnModule Γ R V z :=
  (rfl)

/-- In any finite basis, the inverse comparison is the sum of the scalar coordinate series
tensored with the corresponding basis vectors. -/
theorem tensorProductEquiv_symm_apply [Module.Free R V] [Module.Finite R V]
    {ι : Type*} [Fintype ι] (b : Module.Basis ι R V) (x : HahnModule Γ R V) :
    (tensorProductEquiv Γ R V).symm x =
      ∑ i, ((of R).symm x).map (b.coord i) ⊗ₜ[R] b i := by
  apply (tensorProductEquiv Γ R V).injective
  rw [LinearEquiv.apply_symm_apply, tensorProductEquiv_apply, map_sum]
  simp only [tensorProductToHahnModule_tmul]
  exact (sum_map_coord_smul_single b x).symm

/-- The inverse comparison sends a vector-valued monomial to a pure tensor. -/
@[simp]
theorem tensorProductEquiv_symm_single [Module.Free R V] [Module.Finite R V]
    (g : Γ) (v : V) :
    (tensorProductEquiv Γ R V).symm (of R (single g v)) = single g 1 ⊗ₜ[R] v := by
  apply (tensorProductEquiv Γ R V).injective
  simp

/-- For finite free coefficients, linear maps on module-valued Hahn series are determined
by scalar series times constant vectors. -/
theorem _root_.TauCeti.HahnModule.linearMap_ext_smul_single_zero
    [Module.Free R V] [Module.Finite R V]
    {M : Type*} [AddCommMonoid M] [Module R M]
    {f g : HahnModule Γ R V →ₗ[R] M}
    (h : ∀ (a : HahnSeries Γ R) (v : V), f (a • of R (single 0 v)) =
      g (a • of R (single 0 v))) : f = g := by
  ext x
  obtain ⟨z, rfl⟩ := (tensorProductEquiv Γ R V).surjective x
  induction z using TensorProduct.inductionOn with
  | tmul a v => simpa using h a v
  | add z w hz hw => simp only [map_add, hz, hw]

/-- In any basis of the coefficient module, scalar-series coordinates agree with the
coordinates of the coefficients of the scalar-extension comparison. -/
theorem coeff_equivFinsuppOfBasisRight {ι : Type*} [DecidableEq ι]
    (b : Module.Basis ι R V) (z : HahnSeries Γ R ⊗[R] V) (i : ι) (g : Γ) :
    (TensorProduct.equivFinsuppOfBasisRight b z i).coeff g =
      b.repr (((of R).symm (tensorProductToHahnModule Γ R V z)).coeff g) i := by
  induction z using TensorProduct.inductionOn with
  | tmul f v => simp [mul_comm]
  | add z w hz hw => simp [hz, hw]

/-- The scalar-extension comparison is injective for free coefficient modules, without any
finiteness assumption on a basis. -/
theorem tensorProductToHahnModule_injective [Module.Free R V] :
    Function.Injective (tensorProductToHahnModule Γ R V) := by
  classical
  let b := Module.Free.chooseBasis R V
  intro z w h
  apply (TensorProduct.equivFinsuppOfBasisRight b).injective
  ext i g
  simp only [coeff_equivFinsuppOfBasisRight, h]

/-- All coefficients of a tensor current lie in one finitely generated submodule. This is the
finite-rank obstruction to representing arbitrary vector-valued series by tensor currents. -/
theorem exists_fg_coeff_tensorProductToHahnModule (z : HahnSeries Γ R ⊗[R] V) :
    ∃ S : Submodule R V, S.FG ∧
      ∀ g, ((of R).symm (tensorProductToHahnModule Γ R V z)).coeff g ∈ S := by
  induction z using TensorProduct.inductionOn with
  | tmul f v =>
    refine ⟨R ∙ v, Submodule.fg_span_singleton v, fun g ↦ ?_⟩
    simpa using Submodule.smul_mem (R ∙ v) (f.coeff g) (Submodule.mem_span_singleton_self v)
  | add z w hz hw =>
    obtain ⟨S, hS, hz⟩ := hz
    obtain ⟨T, hT, hw⟩ := hw
    refine ⟨S ⊔ T, hS.sup hT, fun g ↦ ?_⟩
    simpa using Submodule.add_mem_sup (hz g) (hw g)

end HahnModule

namespace HahnModule

section Field

variable {Γ K V : Type*} [AddCommMonoid Γ] [PartialOrder Γ]
  [IsOrderedCancelAddMonoid Γ] [Field K] [AddCommGroup V] [Module K V]

/-- A vector-valued Hahn series comes from scalar extension exactly when all its coefficients
lie in a single finite-dimensional subspace. -/
theorem mem_range_tensorProductToHahnModule_iff (x : HahnModule Γ K V) :
    x ∈ Set.range (tensorProductToHahnModule Γ K V) ↔
      ∃ S : Submodule K V, FiniteDimensional K S ∧
        ∀ g, ((of K).symm x).coeff g ∈ S := by
  constructor
  · rintro ⟨z, rfl⟩
    obtain ⟨S, hS, hz⟩ := exists_fg_coeff_tensorProductToHahnModule z
    exact ⟨S, (Submodule.fg_iff_finiteDimensional S).mp hS, hz⟩
  · rintro ⟨S, hS, hx⟩
    let := hS
    let y : HahnSeries Γ S :=
      { coeff := fun g ↦ ⟨((of K).symm x).coeff g, hx g⟩
        isPWO_support' := ((of K).symm x).isPWO_support.mono (by
          intro g hg
          simpa only [Function.mem_support, HahnSeries.mem_support, ne_eq, Subtype.ext_iff,
            ZeroMemClass.coe_zero]
            using hg) }
    obtain ⟨z, hz⟩ := (tensorProductEquiv Γ K S).surjective (of K y)
    refine ⟨TensorProduct.map (.id : HahnSeries Γ K →ₗ[K] _) S.subtype z, ?_⟩
    apply HahnModule.ext
    funext g
    rw [coeff_tensorProductToHahnModule_map, ← tensorProductEquiv_apply, hz]
    simp [y]

end Field

section Ring

variable {Γ R V : Type*} [AddCommMonoid Γ] [PartialOrder Γ]
  [IsOrderedCancelAddMonoid Γ] [CommRing R] [Nontrivial R] [AddCommGroup V] [Module R V]

/-- A series with an infinite independent family of coefficients is not a tensor current. -/
theorem notMem_range_tensorProductToHahnModule_of_linearIndependent
    {ι : Type*} [Infinite ι] (x : HahnModule Γ R V) (e : ι → Γ)
    (h : LinearIndependent R (fun i ↦ ((of R).symm x).coeff (e i))) :
    x ∉ Set.range (tensorProductToHahnModule Γ R V) := by
  rintro ⟨z, rfl⟩
  obtain ⟨S, hS, hz⟩ := exists_fg_coeff_tensorProductToHahnModule z
  let := Module.Finite.iff_fg.mpr hS
  exact Module.Finite.not_linearIndependent_of_infinite _ (h.codRestrict S fun i ↦ hz (e i))

/-- For free coefficients over a nontrivial commutative ring, scalar extension to Laurent series
is surjective exactly when the coefficient module is finitely generated. Over a field this is
finite-dimensionality, with no characteristic-zero hypothesis. -/
theorem tensorProductToHahnModule_int_surjective_iff [Module.Free R V] :
    Function.Surjective (tensorProductToHahnModule ℤ R V) ↔ Module.Finite R V := by
  classical
  constructor
  · intro hsurj
    by_contra hfinite
    let b := Module.Free.chooseBasis R V
    have : Infinite (Module.Free.ChooseBasisIndex R V) := by
      apply not_finite_iff_infinite.mp
      intro h
      let := h
      exact hfinite (Module.Finite.of_basis b)
    let e := Infinite.natEmbedding (Module.Free.ChooseBasisIndex R V)
    let c : ℤ → V := fun n ↦ if 0 ≤ n then b (e n.toNat) else 0
    have hc : BddBelow (Function.support c) := by
      refine ⟨0, fun n hn ↦ ?_⟩
      by_contra h
      exact hn (by simp [c, h])
    let x : HahnModule ℤ R V := of R (HahnSeries.ofSuppBddBelow c hc)
    have hx (n : ℕ) : ((of R).symm x).coeff (n : ℤ) = b (e n) := by
      simp [x, c]
    have hli : LinearIndependent R (fun n : ℕ ↦ ((of R).symm x).coeff (n : ℤ)) := by
      simpa only [hx, Function.comp_def] using b.linearIndependent.comp e e.injective
    exact notMem_range_tensorProductToHahnModule_of_linearIndependent x
      (fun n : ℕ ↦ (n : ℤ)) hli (hsurj x)
  · intro h
    let := h
    exact (tensorProductToHahnModule_bijective_of_basis (Module.Free.chooseBasis R V)).surjective

end Ring

end HahnModule
