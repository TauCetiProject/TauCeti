/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.ZLattice.Basic
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.IsTensorProduct
public import Mathlib.RingTheory.TensorProduct.IsBaseChangeFree

/-!
# Integral lattices in a real vector space

The combinatorics of a toric variety takes place in a real vector space `V` carrying a
distinguished additive map `i : N →+ V` from an abelian group of integral vectors. For that
picture to determine anything, `N` has to be finite free over `ℤ` and `V` has to be the real
scalar extension of `N` along `i`: the latter is exactly Mathlib's `IsBaseChange ℝ` condition on
the `ℤ`-linear map underlying `i`, and `TauCeti.Toric.IsIntegralLattice` is the name this
development gives this interface.

Injectivity of `i` together with a full real span is strictly weaker and is not enough. The map
`ℤ² →+ ℝ`, `(a, b) ↦ a + √2 * b`, is injective and its image spans `ℝ`, yet its image is dense,
so a ray of `ℝ` can contain lattice vectors of two incomparable lengths and a "primitive
generator" of a ray need not exist. The scalar-extension condition rules this out by forcing the
integral and real ranks to agree.

## Main declarations

* `TauCeti.Toric.IsIntegralLattice`: for finite free `N`, the scalar-extension condition on
  `i : N →+ V`, stated as Mathlib's `IsBaseChange ℝ` for the underlying `ℤ`-linear map.
  `isIntegralLattice_iff` is the equivalent formulation by an `ℝ`-linear equivalence
  `ℝ ⊗[ℤ] N ≃ₗ[ℝ] V` restricting to `i`.
* `TauCeti.Toric.isIntegralLattice_of_basis`: an integral basis of `N` whose image is a real
  basis of `V` exhibits an integral lattice.
* `TauCeti.Toric.IsIntegralLattice.injective`, `TauCeti.Toric.IsIntegralLattice.span_range_eq_top`
  and `TauCeti.Toric.IsIntegralLattice.finrank_eq`: an integral lattice is injective with full
  real span, and the integral rank of `N` equals the real dimension of `V`.
* `TauCeti.Toric.IsIntegralLattice.extend` and `TauCeti.Toric.IsIntegralLattice.eq_extend`: a map
  of integral vectors extends to a unique real-linear map, so the real-linear map accompanying a
  map of lattices is determined by it rather than being extra data.
* `TauCeti.Toric.IsIntegralLattice.isZLattice`: in a normed space the image of an integral
  lattice is discrete, hence a `ZLattice` in Mathlib's sense.

## Implementation notes

`IsIntegralLattice` packages finite freeness of the source with a named specialization of
`IsBaseChange`: it fixes the ring extension `ℤ → ℝ`, takes the bare additive map `i` that the
ambient cone geometry uses, and is the vocabulary in which toric cones, fans and their morphisms
are stated. The `IsIntegralLattice.isBaseChange` projection is the interface that downstream
modules use to reach the whole of Mathlib's base-change API.

## References

The mathematics is §1.2 of D. Cox, J. Little and H. Schenck, *Toric Varieties*, and §1.2 of
W. Fulton, *Introduction to Toric Varieties*.
-/

public section

namespace TauCeti.Toric

open scoped TensorProduct

section Basic

variable {N V : Type*} [AddCommGroup N] [AddCommGroup V] [Module ℝ V] {i : N →+ V}

/-- An additive map `i : N →+ V` from a finite free `ℤ`-module into a real vector space is an
*integral lattice* when it exhibits `V` as the extension of scalars of `N` from `ℤ` to `ℝ`. -/
-- Interface source: `TauCetiRoadmap/AnalyticToricGeometry/Suggested.lean`.
structure IsIntegralLattice (i : N →+ V) : Prop where
  /-- The module of integral vectors is free. -/
  free : Module.Free ℤ N
  /-- The module of integral vectors is finitely generated. -/
  finite : Module.Finite ℤ N
  /-- Extending scalars from `ℤ` to `ℝ` along `i` gives the ambient real vector space. -/
  isBaseChange : IsBaseChange ℝ i.toIntLinearMap

/-- An integral lattice, spelled by the scalar-extension equivalence it provides. -/
theorem isIntegralLattice_iff :
    IsIntegralLattice i ↔ Module.Free ℤ N ∧ Module.Finite ℤ N ∧
      ∃ e : ℝ ⊗[ℤ] N ≃ₗ[ℝ] V, ∀ n : N, e (1 ⊗ₜ[ℤ] n) = i n := by
  refine ⟨fun h ↦ ⟨h.free, h.finite, h.isBaseChange.equiv, fun n ↦ by simp⟩, ?_⟩
  rintro ⟨hfree, hfinite, e, he⟩
  exact ⟨hfree, hfinite, IsBaseChange.of_equiv e he⟩

/-- An integral basis of `N` whose image under `i` is a real basis of `V` exhibits `i` as an
integral lattice. -/
theorem isIntegralLattice_of_basis {n : ℕ} (b : Module.Basis (Fin n) ℤ N)
    (c : Module.Basis (Fin n) ℝ V) (hbc : ∀ j, i (b j) = c j) : IsIntegralLattice i := by
  obtain ⟨e, he⟩ : ∃ e : ℝ ⊗[ℤ] N ≃ₗ[ℝ] V, ∀ j, e (1 ⊗ₜ[ℤ] b j) = i (b j) := by
    refine ⟨(b.baseChange ℝ).equiv c (Equiv.refl (Fin n)), fun j ↦ ?_⟩
    rw [← Module.Basis.baseChange_apply ℝ b j, Module.Basis.equiv_apply]
    exact (hbc j).symm
  refine isIntegralLattice_iff.2
    ⟨Module.Free.of_basis b, Module.Finite.of_basis b, e, fun n ↦ ?_⟩
  exact LinearMap.congr_fun
    (b.ext fun j ↦ he j : (e.restrictScalars ℤ).comp (TensorProduct.mk ℤ ℝ N 1)
      = i.toIntLinearMap) n

/-- An integral lattice is injective. -/
theorem IsIntegralLattice.injective (h : IsIntegralLattice i) :
    Function.Injective i := by
  let _ := h.free
  obtain ⟨e, he⟩ := (isIntegralLattice_iff.1 h).2.2
  intro x y hxy
  refine Module.Flat.tensorProduct_mk_injective ℤ N ℝ (e.injective ?_)
  simpa only [TensorProduct.mk_apply, he] using hxy

/-- The image of an integral lattice spans the ambient real vector space. -/
theorem IsIntegralLattice.span_range_eq_top (h : IsIntegralLattice i) :
    Submodule.span ℝ (Set.range i) = ⊤ := by
  refine top_unique fun v _ ↦ ?_
  refine h.isBaseChange.inductionOn v _ (Submodule.zero_mem _)
    (fun n ↦ Submodule.subset_span ⟨n, rfl⟩) (fun r _ hn ↦ Submodule.smul_mem _ r hn)
    (fun _ _ h₁ h₂ ↦ Submodule.add_mem _ h₁ h₂)

/-- The integral rank of the lattice equals the real dimension of the ambient space. -/
theorem IsIntegralLattice.finrank_eq (h : IsIntegralLattice i) :
    Module.finrank ℤ N = Module.finrank ℝ V := by
  let _ := h.free
  rw [← Module.finrank_baseChange (R := ℝ) (S := ℤ) (M' := N),
    h.isBaseChange.equiv.finrank_eq]

/-- An integral lattice sits in a finite-dimensional real vector space. -/
theorem IsIntegralLattice.finiteDimensional (h : IsIntegralLattice i) :
    FiniteDimensional ℝ V := by
  let _ := h.finite
  exact Module.Finite.equiv h.isBaseChange.equiv

/-- The range of an integral lattice is the `ℤ`-span of the real basis attached to an integral
basis of `N`. -/
theorem IsIntegralLattice.range_eq_span {ι : Type*} (h : IsIntegralLattice i)
    (b : Module.Basis ι ℤ N) :
    LinearMap.range i.toIntLinearMap = Submodule.span ℤ (Set.range (h.isBaseChange.basis b)) := by
  rw [LinearMap.range_eq_map, ← b.span_eq, Submodule.map_span, ← Set.range_comp]
  exact congrArg (Submodule.span ℤ) (congrArg Set.range (funext fun j ↦ by
    simpa only [Function.comp_apply, AddMonoidHom.coe_toIntLinearMap] using
      (h.isBaseChange.basis_apply b j).symm))

end Basic

/-! ### Maps of lattices -/

section Naturality

variable {N N' N'' V V' V'' : Type*} [AddCommGroup N] [AddCommGroup N'] [AddCommGroup N'']
  [AddCommGroup V] [AddCommGroup V'] [AddCommGroup V''] [Module ℝ V] [Module ℝ V'] [Module ℝ V'']
  {i : N →+ V} {i' : N' →+ V'} {i'' : N'' →+ V''}

/-- The real-linear map extending a map `f : N →+ N'` of integral vectors. -/
noncomputable def IsIntegralLattice.extend (h : IsIntegralLattice i) (i' : N' →+ V')
    (f : N →+ N') : V →ₗ[ℝ] V' :=
  h.isBaseChange.lift (i'.toIntLinearMap.comp f.toIntLinearMap)

@[simp]
theorem IsIntegralLattice.extend_apply (h : IsIntegralLattice i) (i' : N' →+ V') (f : N →+ N')
    (n : N) : h.extend i' f (i n) = i' (f n) :=
  h.isBaseChange.lift_eq _ n

/-- A real-linear map compatible with a map of integral vectors is *the* extension of it. This is
what makes the real-linear part of a map of lattices determined rather than chosen. -/
theorem IsIntegralLattice.eq_extend (h : IsIntegralLattice i) {f : N →+ N'} {g : V →ₗ[ℝ] V'}
    (hg : ∀ n, g (i n) = i' (f n)) : g = h.extend i' f :=
  h.isBaseChange.algHom_ext g (h.extend i' f) fun n ↦ by
    simp only [AddMonoidHom.coe_toIntLinearMap, hg, IsIntegralLattice.extend_apply]

@[simp]
theorem IsIntegralLattice.extend_id (h : IsIntegralLattice i) :
    h.extend i (AddMonoidHom.id N) = LinearMap.id :=
  (h.eq_extend fun _ ↦ rfl).symm

@[simp]
theorem IsIntegralLattice.extend_comp (h : IsIntegralLattice i) (h' : IsIntegralLattice i')
    (f : N →+ N') (f' : N' →+ N'') :
    (h'.extend i'' f').comp (h.extend i' f) = h.extend i'' (f'.comp f) :=
  h.eq_extend (i' := i'') (f := f'.comp f) fun n ↦ by simp

/-- Being an integral lattice transfers along an isomorphism of the integral vectors together
with a compatible real-linear equivalence. -/
theorem isIntegralLattice_congr (f : N ≃+ N') (e : V ≃ₗ[ℝ] V')
    (hfe : ∀ n, e (i n) = i' (f n)) : IsIntegralLattice i ↔ IsIntegralLattice i' := by
  have hbase : IsBaseChange ℝ i.toIntLinearMap ↔ IsBaseChange ℝ i'.toIntLinearMap :=
    IsBaseChange.iff_of_equiv_comm f.toIntLinearEquiv e
      (by ext n; exact (hfe n).symm)
  constructor
  · intro h
    exact ⟨(Module.Free.iff_of_equiv f.toIntLinearEquiv).1 h.free,
      (Module.Finite.equiv_iff f.toIntLinearEquiv).1 h.finite, hbase.1 h.isBaseChange⟩
  · intro h
    exact ⟨(Module.Free.iff_of_equiv f.toIntLinearEquiv).2 h.free,
      (Module.Finite.equiv_iff f.toIntLinearEquiv).2 h.finite, hbase.2 h.isBaseChange⟩

end Naturality

/-! ### Discreteness -/

section Discrete

variable {N V : Type*} [AddCommGroup N] [NormedAddCommGroup V] [NormedSpace ℝ V] {i : N →+ V}

/-- The image of an integral lattice is a discrete subgroup of a normed real vector space; this
is what fails for an injective map with dense image. -/
theorem IsIntegralLattice.discreteTopology (h : IsIntegralLattice i) :
    DiscreteTopology (LinearMap.range i.toIntLinearMap) := by
  let _ := h.free
  let _ := h.finite
  rw [h.range_eq_span (Module.Free.chooseBasis ℤ N)]
  infer_instance

/-- The image of an integral lattice is a `ℤ`-lattice in Mathlib's sense. -/
theorem IsIntegralLattice.isZLattice (h : IsIntegralLattice i) :
    haveI := h.discreteTopology
    IsZLattice ℝ (LinearMap.range i.toIntLinearMap) :=
  haveI := h.discreteTopology
  ⟨by rw [LinearMap.coe_range]; exact h.span_range_eq_top⟩

end Discrete

/-! ### The standard lattice -/

/-- The standard lattice `ℤ^n ⊆ ℝ^n` given by the coordinatewise integer cast. -/
theorem isIntegralLattice_intCast (n : ℕ) :
    IsIntegralLattice ((Int.castAddHom ℝ).compLeft (Fin n)) :=
  isIntegralLattice_of_basis (Pi.basisFun ℤ (Fin n)) (Pi.basisFun ℝ (Fin n)) fun j ↦ by
    ext k
    simp [Pi.basisFun_apply, Pi.single_apply, apply_ite]

end TauCeti.Toric
