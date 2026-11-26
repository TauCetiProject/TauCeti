/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.EuclideanDomain.Int
public import Mathlib.Algebra.Module.Lattice.Full
public import Mathlib.LinearAlgebra.FreeModule.Finite.CardQuotient
public import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import TauCeti.LinearAlgebra.TensorProduct.ScalarExtension
import Mathlib.Algebra.Module.LocalizedModule.Int
import Mathlib.LinearAlgebra.Charpoly.BaseChange
import Mathlib.RingTheory.Localization.Finiteness
import Mathlib.RingTheory.Localization.Submodule
import TauCeti.Algebra.Module.LocalizedModule.Submodule
import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Basis

/-!
# Full submodule lattices

This file provides generic results about full submodules over commutative algebras. It relates
bases and ranks of full submodules to their ambient spaces. It also extends integral linear
equivalences between full submodules to linear equivalences of their ambient modules, and proves
that surjective linear maps preserve full lattices over fraction fields, as do finite
products. Injective linear maps pull back full lattices over localizations of Noetherian
commutative rings. Scalar extension of a free full lattice recovers its ambient module. Finally,
the stabilizer of a free full lattice `L` in the ambient automorphism group is the automorphism
group of `L`, hence `GL_n` of the coefficients in a basis of `L`.

## Main declarations

* `Module.Basis.span_range_extendOfIsFullLattice`: the span of an extended lattice basis is the
  lattice.
* `Module.Basis.extendOfIsFullLattice_repr_coe`: the ambient coordinates of a lattice vector are
  the images of its lattice coordinates.
* `Module.Basis.toAddSubgroup_eq_closure_range_extendOfIsFullLattice`: the additive
  closure of an extended lattice basis is the lattice's underlying additive subgroup.
* `Submodule.IsFullLattice.relIndex_ne_zero`: a full `ℤ`-lattice has finite index in every
  full `ℤ`-lattice.
* `Submodule.IsFullLattice.relIndex_span_eq_abs_det_mul`: the indices of a full `ℤ`-lattice
  in the `ℤ`-spans of two `ℚ`-bases differ by the determinant of the change of basis.
* `Submodule.toAddSubgroup_submoduleOf`: taking the underlying additive subgroup commutes
  with restricting a submodule to another submodule.
* `Submodule.isFullLattice_span`: the span of a finite set spanning the ambient module is a full
  lattice.
* `Submodule.isFullLattice_comap_of_isLocalization`: pullback of a full lattice along an injective
  linear map over a localization of a Noetherian commutative ring.
* `Submodule.isFullLattice_comap`: the specialization to the total ring of fractions.
* `Module.Finite.of_isFullLattice`: a module containing a full lattice is finite.
* `Submodule.finrank_eq_finrank`: a full lattice and its ambient space have the
  same finrank.
* `Submodule.IsFullLattice.pi`: the product of a finite family of full lattices is a full lattice.
* `Submodule.IsFullLattice.prod`: the product of two full lattices is a full lattice.
* `LinearEquiv.extendOfIsFullLattice`: extension of an `R`-linear equivalence between
  full submodules to their ambient `K`-modules.
* `Submodule.isBaseChange_subtype`: the inclusion of a free full lattice
  submodule into its ambient module is a base change.
* `LinearMap.det_eq_algebraMap_det_of_isFullLattice`: an endomorphism of the ambient space which
  restricts to an endomorphism of a free full lattice has the determinant of that restriction.
* `Submodule.rationalizationEquiv`: the canonical equivalence from the scalar extension
  of a free full lattice submodule to its ambient module.
* `Submodule.IsLattice.exists_ne_zero_smul_mem`: some nonzero multiple of every ambient vector
  lies in a submodule spanning the ambient space over the fraction field, such as a full lattice.
* `Submodule.exists_ne_zero_smul_mem_baseChange`: the same holds for every element of a scalar
  extension and the base change of such a submodule.
* `Submodule.IsLattice.exists_ne_zero_forall_smul_mem`: a single nonzero scalar multiplies a
  finitely generated submodule into a submodule spanning the ambient space over `K`.
* `Submodule.IsFullLattice.exists_maximalIdeal_pow_smul_le`: over a discrete valuation ring, a power
  of the maximal ideal multiplies a finitely generated submodule into a full lattice.
* `Submodule.stabilizerMulEquiv`: the stabilizer of a free full lattice `L` in `V ≃ₗ[K] V` is
  isomorphic to `L ≃ₗ[R] L` by restriction.
* `Module.Basis.stabilizerMulEquivGL`: in an `R`-basis of `L`, that stabilizer is `GL ι R`, and
  `Module.Basis.map_stabilizerMulEquivGL_apply` reads its matrices in the extended `K`-basis.
* `Module.Basis.mem_stabilizer_iff_exists_map_eq_toMatrix`: an ambient automorphism stabilizes
  `L` exactly when its matrix in the extended basis comes from `GL ι R`.
* `TensorProduct.rationalizationEquiv_baseChange_unitTmulEquiv`: rationalizing that
  unit-tensor lattice returns the scalar extension one started from.

## References

* See N. Bourbaki, *Commutative Algebra*, Chapter VII, §4 for lattice theory over Dedekind domains.
-/

public section

open Module TensorProduct

namespace TauCeti

universe u v w

section

variable {R K V : Type*} [CommRing R] [CommRing K] [Algebra R K]
variable [AddCommGroup V] [Module R V] [Module K V] [IsScalarTower R K V]

/-- The `R`-span of the ambient `K`-basis obtained from an `R`-basis of a lattice is the lattice
itself. -/
theorem _root_.Module.Basis.span_range_extendOfIsFullLattice {κ : Type*} {N : Submodule R V}
    [N.IsFullLattice K] (b : Basis κ R N) :
    Submodule.span R (Set.range (b.extendOfIsFullLattice K)) = N := by
  have hrange : Set.range (b.extendOfIsFullLattice K) = Set.range (N.subtype ∘ b) :=
    congrArg Set.range (funext fun i ↦ Basis.extendOfIsFullLattice_apply K b i)
  rw [hrange, Set.range_comp, ← Submodule.map_span, b.span_eq,
    Submodule.map_top, Submodule.range_subtype]

variable (K) in
/-- The coordinates of a lattice vector in the ambient basis extended from a lattice basis are the
images of its lattice coordinates. -/
@[simp]
theorem _root_.Module.Basis.extendOfIsFullLattice_repr_coe {N : Submodule R V} [N.IsFullLattice K]
    {κ : Type*} (b : Basis κ R N) (x : N) (i : κ) :
    (b.extendOfIsFullLattice K).repr x i = algebraMap R K (b.repr x i) := by
  -- Both sides are `R`-linear in `x`, so it suffices to compare them on the basis `b`.
  let f₁ : N →ₗ[R] K := ((b.extendOfIsFullLattice K).coord i).restrictScalars R ∘ₗ N.subtype
  let f₂ : N →ₗ[R] K := Algebra.linearMap R K ∘ₗ b.coord i
  have h : f₁ = f₂ := b.ext fun j => by
    classical
    have hj : ((b j : N) : V) = b.extendOfIsFullLattice K j :=
      (Basis.extendOfIsFullLattice_apply K b j).symm
    simp only [f₁, f₂, LinearMap.comp_apply, Submodule.subtype_apply,
      LinearMap.restrictScalars_apply, hj, Basis.coord_apply, Basis.repr_self,
      Algebra.linearMap_apply, Finsupp.single_apply]
    split_ifs <;> simp
  exact LinearMap.congr_fun h x

/-- The additive subgroup generated by an extended basis of a full `ℤ`-submodule is the submodule's
underlying additive subgroup. -/
theorem _root_.Module.Basis.toAddSubgroup_eq_closure_range_extendOfIsFullLattice
    {W : Type*} [AddCommGroup W] [Module ℚ W] {N : Submodule ℤ W} [N.IsFullLattice ℚ]
    {κ : Type*} (b : Basis κ ℤ N) :
    N.toAddSubgroup = AddSubgroup.closure (Set.range (b.extendOfIsFullLattice ℚ)) := by
  apply AddSubgroup.toIntSubmodule.injective
  rw [AddSubgroup.toIntSubmodule_closure, Module.Basis.span_range_extendOfIsFullLattice,
    Submodule.toIntSubmodule_toAddSubgroup, Submodule.restrictScalars_self]

end

section

variable {R A V : Type*} [CommRing R] [CommRing A] [Algebra R A]
variable [AddCommGroup V] [Module R V] [Module A V] [IsScalarTower R A V]

/-- A module containing a full lattice is finite: the generators of the lattice span it. -/
theorem _root_.Module.Finite.of_isFullLattice (M : Submodule R V) [M.IsFullLattice A] :
    Module.Finite A V := by
  obtain ⟨s, hs⟩ := Submodule.IsLattice.fg (A := A) (M := M)
  exact ⟨⟨s, by rw [← Submodule.span_span_of_tower R, hs, Submodule.IsFullLattice.span_eq_top]⟩⟩

end

section

/-- Taking the underlying additive subgroup commutes with restricting a submodule to another
submodule. -/
theorem _root_.Submodule.toAddSubgroup_submoduleOf {R V : Type*} [Ring R] [AddCommGroup V]
    [Module R V] (p q : Submodule R V) :
    (p.submoduleOf q).toAddSubgroup = p.toAddSubgroup.addSubgroupOf q.toAddSubgroup := rfl

variable {V : Type*} [AddCommGroup V] [Module ℚ V]

/-- A full `ℤ`-submodule has finite index in every full `ℤ`-submodule: its index is that of its
intersection with it. -/
theorem _root_.Submodule.IsFullLattice.relIndex_ne_zero {N M : Submodule ℤ V} [N.IsFullLattice ℚ]
    [M.IsFullLattice ℚ] : N.toAddSubgroup.relIndex M.toAddSubgroup ≠ 0 := by
  classical
  -- needed for the `IsFullLattice.inf` instance on `N ⊓ M`
  have := Module.Finite.of_isFullLattice (R := ℤ) (A := ℚ) N
  have key {P : Submodule ℤ V} [P.IsFullLattice ℚ] (hle : P ≤ M) :
      P.toAddSubgroup.relIndex M.toAddSubgroup ≠ 0 := by
    have := _root_.Submodule.IsLattice.free ℚ M
    have := _root_.Submodule.IsLattice.finite ℚ M
    have := _root_.Submodule.IsLattice.free ℚ P
    let bM := Module.Free.chooseBasis ℤ M
    let eM := bM.extendOfIsFullLattice ℚ
    let bP := (Module.Free.chooseBasis ℤ P).reindex
      (((Module.Free.chooseBasis ℤ P).extendOfIsFullLattice ℚ).indexEquiv eM)
    have hidx := AddSubgroup.relIndex_eq_abs_det _ _ ((Submodule.toAddSubgroup_le _ _).mpr hle)
      (bP.extendOfIsFullLattice ℚ) eM bP.toAddSubgroup_eq_closure_range_extendOfIsFullLattice
      bM.toAddSubgroup_eq_closure_range_extendOfIsFullLattice
    intro h
    rw [h, Nat.cast_zero, eq_comm, abs_eq_zero] at hidx
    exact (eM.isUnit_det _).ne_zero hidx
  rw [← AddSubgroup.inf_relIndex_right]
  exact key (P := N ⊓ M) inf_le_right

/-- **Indices of a common full sublattice differ by a determinant.** If a full `ℤ`-submodule `N`
lies in the `ℤ`-spans of two `ℚ`-bases `b` and `c`, then its index in the span of `b` is
`|b.det c|` times its index in the span of `c`. -/
theorem _root_.Submodule.IsFullLattice.relIndex_span_eq_abs_det_mul {ι : Type*} [Fintype ι]
    [DecidableEq ι] {N : Submodule ℤ V} [N.IsFullLattice ℚ] (b c : Basis ι ℚ V)
    (hb : N ≤ Submodule.span ℤ (Set.range b)) (hc : N ≤ Submodule.span ℤ (Set.range c)) :
    (N.toAddSubgroup.relIndex (Submodule.span ℤ (Set.range b)).toAddSubgroup : ℚ) =
      |b.det c| * N.toAddSubgroup.relIndex (Submodule.span ℤ (Set.range c)).toAddSubgroup := by
  have := _root_.Submodule.IsLattice.free ℚ N
  have := _root_.Submodule.IsLattice.finite ℚ N
  let bN := (Module.Free.chooseBasis ℤ N).reindex
    (((Module.Free.chooseBasis ℤ N).extendOfIsFullLattice ℚ).indexEquiv b)
  have hN := bN.toAddSubgroup_eq_closure_range_extendOfIsFullLattice
  rw [AddSubgroup.relIndex_eq_abs_det _ _ ((Submodule.toAddSubgroup_le _ _).mpr hb) _ b hN
      (Submodule.span_int_eq_addSubgroupClosure _),
    AddSubgroup.relIndex_eq_abs_det _ _ ((Submodule.toAddSubgroup_le _ _).mpr hc) _ c hN
      (Submodule.span_int_eq_addSubgroupClosure _), ← abs_mul, Basis.det_mul_det]

end

section

variable {R : Type*} {K : Type*} {V : Type u} {W : Type v}
variable [CommRing R] [CommRing K] [Algebra R K]
variable [AddCommGroup V] [Module R V] [Module K V] [IsScalarTower R K V]
variable [AddCommGroup W] [Module R W] [Module K W] [IsScalarTower R K W]

/-- Extend an `R`-linear equivalence between full submodules uniquely to their ambient
`K`-modules. -/
noncomputable def _root_.LinearEquiv.extendOfIsFullLattice {S : Submodule R V} {T : Submodule R W}
    [S.IsFullLattice K] [T.IsFullLattice K] [Module.Free R S] (e : S ≃ₗ[R] T) : V ≃ₗ[K] W :=
  let b := Module.Free.chooseBasis R S
  (b.extendOfIsFullLattice K).equiv ((b.map e).extendOfIsFullLattice K) (Equiv.refl _)

/-- The ambient extension of a full-submodule equivalence agrees with it on the submodule. -/
@[simp]
theorem _root_.LinearEquiv.extendOfIsFullLattice_apply {S : Submodule R V} {T : Submodule R W}
    [S.IsFullLattice K] [T.IsFullLattice K] [Module.Free R S] (e : S ≃ₗ[R] T) (x : S) :
    LinearEquiv.extendOfIsFullLattice (K := K) e (x : V) = (e x : W) := by
  let b := Module.Free.chooseBasis R S
  have h :
      (LinearEquiv.extendOfIsFullLattice (K := K) e).toLinearMap.restrictScalars R ∘ₗ S.subtype =
        T.subtype ∘ₗ e.toLinearMap := by
    apply b.ext
    intro i
    dsimp only [b]
    simp only [LinearMap.comp_apply, LinearMap.restrictScalars_apply, Submodule.subtype_apply,
      LinearEquiv.coe_toLinearMap]
    rw [← Basis.extendOfIsFullLattice_apply K (Module.Free.chooseBasis R S) i]
    -- Expose the constructed basis equivalence so `Basis.equiv_apply` can identify its values.
    unfold LinearEquiv.extendOfIsFullLattice
    rw [Basis.equiv_apply, Basis.extendOfIsFullLattice_apply, Basis.map_apply, Equiv.refl_apply]
  exact LinearMap.congr_fun h x

/-- A `K`-linear equivalence extending a given equivalence of full submodules is the
canonical extension. -/
theorem _root_.LinearEquiv.eq_extendOfIsFullLattice {S : Submodule R V} {T : Submodule R W}
    [S.IsFullLattice K] [T.IsFullLattice K] [Module.Free R S] (e : S ≃ₗ[R] T) (f : V ≃ₗ[K] W)
    (h : ∀ x : S, f (x : V) = (e x : W)) : f = LinearEquiv.extendOfIsFullLattice (K := K) e := by
  apply LinearEquiv.toLinearMap_injective
  apply (Module.Free.chooseBasis R S).extendOfIsFullLattice K |>.ext
  intro i
  rw [Basis.extendOfIsFullLattice_apply]
  exact (h (Module.Free.chooseBasis R S i)).trans
    (LinearEquiv.extendOfIsFullLattice_apply e (Module.Free.chooseBasis R S i)).symm

/-- The ambient extension maps the source full submodule onto the target full submodule. -/
theorem _root_.LinearEquiv.extendOfIsFullLattice_map {S : Submodule R V} {T : Submodule R W}
    [S.IsFullLattice K] [T.IsFullLattice K] [Module.Free R S] (e : S ≃ₗ[R] T) :
    S.map ((LinearEquiv.extendOfIsFullLattice (K := K) e).restrictScalars R).toLinearMap = T := by
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    have hmem : (e (⟨x, hx⟩ : S) : W) ∈ T := (e ⟨x, hx⟩).property
    rw [← LinearEquiv.extendOfIsFullLattice_apply (K := K)] at hmem
    simpa only [LinearEquiv.restrictScalars_apply, LinearEquiv.coe_toLinearMap] using hmem
  · intro y hy
    let yT : T := ⟨y, hy⟩
    let xS : S := e.symm yT
    refine ⟨(xS : V), xS.property, ?_⟩
    simpa only [LinearEquiv.restrictScalars_apply, LinearEquiv.coe_toLinearMap,
      LinearEquiv.extendOfIsFullLattice_apply] using congr_arg Subtype.val (e.apply_symm_apply yT)

end

end TauCeti

namespace Submodule

section Rationalization

variable {R : Type u} {K : Type v} {V' : Type w}
variable [CommRing R]
variable [CommRing K] [Algebra R K]
variable [AddCommGroup V'] [Module R V'] [Module K V'] [IsScalarTower R K V']

/-- The inclusion of a free full lattice submodule into its ambient module exhibits that module
as base change from `R` to `K`. -/
theorem isBaseChange_subtype (S : Submodule R V') [Module.Free R S] [S.IsFullLattice K] :
    IsBaseChange K S.subtype := by
  let b := Module.Free.chooseBasis R S
  let e : K ⊗[R] S ≃ₗ[K] V' :=
    (b.baseChange K).equiv (b.extendOfIsFullLattice K) (Equiv.refl _)
  have hmap : (e.toLinearMap.restrictScalars R).comp (TensorProduct.mk R K S 1) =
      S.subtype := by
    apply b.ext
    intro i
    simp only [LinearMap.comp_apply, LinearMap.restrictScalars_apply, TensorProduct.mk_apply,
      LinearEquiv.coe_coe, Submodule.subtype_apply]
    rw [← Module.Basis.baseChange_apply K b i, Basis.equiv_apply,
      Basis.extendOfIsFullLattice_apply, Equiv.refl_apply]
  exact IsBaseChange.of_equiv e fun x ↦ DFunLike.congr_fun hmap x

/-- The canonical equivalence from the scalar extension of a free full lattice submodule to its
ambient module. -/
noncomputable def rationalizationEquiv (S : Submodule R V') [Module.Free R S] [S.IsFullLattice K] :
    K ⊗[R] S ≃ₗ[K] V' :=
  (isBaseChange_subtype S).equiv

/-- The rationalization equivalence sends a pure tensor to scalar multiplication of the embedded
lattice vector. This equation characterizes the equivalence. -/
@[simp]
theorem rationalizationEquiv_tmul (S : Submodule R V') [Module.Free R S] [S.IsFullLattice K]
    (k : K) (x : S) : rationalizationEquiv S (k ⊗ₜ[R] x) = k • (x : V') :=
  (isBaseChange_subtype S).equiv_tmul k x

/-- The inverse rationalization equivalence sends an embedded lattice vector to the corresponding
unit pure tensor. -/
@[simp]
theorem rationalizationEquiv_symm_coe (S : Submodule R V') [Module.Free R S] [S.IsFullLattice K]
    (x : S) : (rationalizationEquiv (K := K) S).symm (x : V') = 1 ⊗ₜ[R] x :=
  (isBaseChange_subtype S).equiv_symm_apply x

/-- A `K`-linear endomorphism of the ambient space which restricts to an endomorphism `g` of a
free full lattice `S` has the determinant of `g`, read in `K`. -/
theorem _root_.LinearMap.det_eq_algebraMap_det_of_isFullLattice {S : Submodule R V'}
    [Module.Free R S] [S.IsFullLattice K] (f : V' →ₗ[K] V') (g : S →ₗ[R] S)
    (h : ∀ x : S, f x = g x) : LinearMap.det f = algebraMap R K (LinearMap.det g) := by
  -- Rationalization identifies `f` with the base change of `g`.
  have := IsLattice.finite K S
  have hconj : f = (rationalizationEquiv S).toLinearMap ∘ₗ g.baseChange K ∘ₗ
      (rationalizationEquiv (K := K) S).symm.toLinearMap := by
    rw [← LinearMap.comp_assoc, LinearEquiv.eq_comp_toLinearMap_symm]
    ext x
    simp [h]
  rw [hconj, LinearMap.det_conj, LinearMap.det_baseChange]

end Rationalization

section Map

variable {R A : Type*} {V : Type u} {W : Type v}
variable [CommRing R] [Field A] [Algebra R A] [IsFractionRing R A]
variable [AddCommGroup V] [Module R V] [Module A V] [IsScalarTower R A V]
variable [AddCommGroup W] [Module R W] [Module A W] [IsScalarTower R A W]

/-- A surjective linear map over the fraction field sends a full lattice to a full lattice. -/
theorem isFullLattice_map (S : Submodule R V) [S.IsFullLattice A] (f : V →ₗ[A] W)
    (hf : Function.Surjective f) : (S.map (f.restrictScalars R)).IsFullLattice A where
  __ := IsLattice.of_fg A ((IsLattice.fg A S).map (f.restrictScalars R))
  span_eq_top := by
    simp [Submodule.map_coe, Submodule.span_image, _root_.Submodule.IsFullLattice.span_eq_top,
      LinearMap.range_eq_top.mpr hf]

end Map

section Comap

variable {R A : Type*} {V : Type u} {W : Type v}
variable [CommRing R] [CommRing A] [Algebra R A]
variable [AddCommGroup V] [Module R V] [Module A V] [IsScalarTower R A V]
variable [AddCommGroup W] [Module R W] [Module A W] [IsScalarTower R A W]

/-- Pulling back a full lattice along an injective linear map over a localization of a
Noetherian commutative ring gives a full lattice. -/
theorem isFullLattice_comap_of_isLocalization (M : Submonoid R) [IsLocalization M A]
    [IsNoetherianRing R] (S : Submodule R V) [S.IsFullLattice A] (f : W →ₗ[A] V)
    (hf : Function.Injective f) : (S.comap (f.restrictScalars R)).IsFullLattice A where
  fg := Submodule.fg_of_fg_map_injective (f.restrictScalars R)
    (fun _ _ h ↦ hf (by simpa using h))
    (Submodule.FG.of_le (IsLattice.fg A S) (Submodule.map_comap_le _ _))
  linearIndepOn s hs hli := by
    -- Transport `s` into `S`, where `R`-independence implies `A`-independence, and back.
    have hR : LinearIndepOn R id (f '' s) :=
      LinearIndepOn.id_image (v := f.restrictScalars R)
        (hli.map' (f.restrictScalars R) (LinearMap.ker_eq_bot_of_injective hf))
    have hA : LinearIndepOn A id (f '' s) :=
      IsLattice.linearIndepOn (f '' s) (Set.image_subset_iff.mpr hs) hR
    exact LinearIndepOn.of_comp f ((linearIndepOn_iff_image hf.injOn).mpr hA)
  span_eq_top := by
    apply top_unique
    intro w _
    obtain ⟨r, hr⟩ := multiple_mem_span_of_mem_localization_span M A (S : Set V) (f w)
      (by rw [_root_.Submodule.IsFullLattice.span_eq_top]; exact Submodule.mem_top)
    have hmem : (r : R) • w ∈ S.comap (f.restrictScalars R) := by
      simpa only [Submonoid.smul_def, Submodule.span_eq, Submodule.mem_comap,
        LinearMap.restrictScalars_apply, LinearMap.map_smul_of_tower] using hr
    have hspan : algebraMap R A (r : R) • w ∈
        Submodule.span A (S.comap (f.restrictScalars R) : Set W) := by
      rw [algebraMap_smul]
      exact Submodule.subset_span hmem
    exact (Submodule.smul_mem_iff_of_isUnit _ (IsLocalization.map_units A r)).mp hspan

/-- Pulling back a full lattice along an injective linear map over the total ring of fractions
of a Noetherian commutative ring gives a full lattice. -/
theorem isFullLattice_comap [IsFractionRing R A] [IsNoetherianRing R]
    (S : Submodule R V) [S.IsFullLattice A] (f : W →ₗ[A] V) (hf : Function.Injective f) :
    (S.comap (f.restrictScalars R)).IsFullLattice A :=
  isFullLattice_comap_of_isLocalization (nonZeroDivisors R) S f hf

end Comap

section Pi

variable {R A : Type*} [CommRing R] [Field A] [Algebra R A] [IsFractionRing R A]
variable {ι : Type*} [Finite ι] {V : ι → Type*} [∀ i, AddCommGroup (V i)] [∀ i, Module R (V i)]
  [∀ i, Module A (V i)] [∀ i, IsScalarTower R A (V i)]

/-- The families all of whose values lie in full lattices form a full lattice of the product. -/
instance IsFullLattice.pi (M : ∀ i, Submodule R (V i)) [∀ i, (M i).IsFullLattice A] :
    (Submodule.pi Set.univ M).IsFullLattice A where
  __ := IsLattice.of_fg A (Submodule.fg_pi fun i ↦ IsLattice.fg A (M i))
  span_eq_top := by
    classical
    cases nonempty_fintype ι
    rw [eq_top_iff]
    intro x _
    rw [← Finset.univ_sum_single x]
    refine Submodule.sum_mem _ fun i _ ↦ ?_
    have hx : x i ∈ Submodule.span A (M i : Set (V i)) := by
      rw [_root_.Submodule.IsFullLattice.span_eq_top]
      exact Submodule.mem_top
    have hmap : Submodule.map (LinearMap.single A V i) (Submodule.span A (M i : Set (V i))) ≤
        Submodule.span A (Submodule.pi Set.univ M : Set (∀ i, V i)) := by
      rw [Submodule.map_span, Submodule.span_le]
      rintro _ ⟨v, hv, rfl⟩
      exact Submodule.subset_span (Submodule.le_comap_single_pi M hv)
    exact hmap (Submodule.mem_map_of_mem hx)

end Pi

section Prod

variable {R A V W : Type*} [CommRing R] [Field A] [Algebra R A] [IsFractionRing R A]
  [AddCommGroup V] [Module R V] [Module A V] [IsScalarTower R A V]
  [AddCommGroup W] [Module R W] [Module A W] [IsScalarTower R A W]

/-- The product of two full lattices is a full lattice of the product. -/
instance IsFullLattice.prod (M : Submodule R V) (N : Submodule R W) [M.IsFullLattice A]
    [N.IsFullLattice A] : (M.prod N).IsFullLattice A where
  __ := IsLattice.of_fg A ((IsLattice.fg A M).prod (IsLattice.fg A N))
  span_eq_top := by
    rw [Submodule.prod_coe, Submodule.span_prod_eq (R := A) M.zero_mem N.zero_mem,
      _root_.Submodule.IsFullLattice.span_eq_top, _root_.Submodule.IsFullLattice.span_eq_top,
      Submodule.prod_top]

end Prod

section Span

variable {R A V : Type*} [CommRing R] [Field A] [Algebra R A] [IsFractionRing R A]
variable [AddCommGroup V] [Module R V] [Module A V] [IsScalarTower R A V]

/-- The `R`-span of a finite set spanning `V` over `A` is a full lattice. In particular every
finite-dimensional vector space contains a lattice, the span of a basis. -/
theorem isFullLattice_span {s : Set V} (hs : s.Finite) (hspan : span A s = ⊤) :
    (span R s).IsFullLattice A where
  __ := IsLattice.of_fg A ⟨hs.toFinset, by simp⟩
  span_eq_top := by rw [span_span_of_tower, hspan]

end Span

section Squeeze

variable {V : Type*} [AddCommGroup V] [Module ℚ V]

open scoped Pointwise in
/-- A submodule `M` of `V` squeezed between `D⁻¹ • N` and `D • N` for a nonzero integer `D` is a
full lattice when `N` is. -/
theorem IsFullLattice.of_nsmul_mem_of_nsmul_mem {N M : Submodule ℤ V} [N.IsFullLattice ℚ]
    {D : ℕ} (hD0 : D ≠ 0) (hNM : ∀ v ∈ N, D • v ∈ M) (hMN : ∀ v ∈ M, D • v ∈ N) :
    M.IsFullLattice ℚ := by
  have := IsLattice.finite ℚ N
  have hinj : Function.Injective (DistribSMul.toLinearMap ℤ V (D : ℤ)) := fun x y h ↦ by
    simp only [DistribSMul.toLinearMap_apply, natCast_zsmul, ← Nat.cast_smul_eq_nsmul ℚ] at h
    exact smul_right_injective V (Nat.cast_ne_zero.mpr hD0) h
  have hfg : M.FG := fg_of_fg_map_injective _ hinj
    (FG.of_le_of_isNoetherian (T := N) (map_le_iff_le_comap.mpr fun v hv ↦ by
      simpa using hMN v hv))
  let a : ℚˣ := Units.mk0 (D : ℚ) (Nat.cast_ne_zero.mpr hD0)
  refine IsFullLattice.of_le_of_fg ℚ (M := a • N) (fun x hx ↦ ?_) hfg
  obtain ⟨v, hv, rfl⟩ := mem_smul_pointwise_iff_exists _ _ _ |>.mp hx
  simpa [a, Units.smul_def, Nat.cast_smul_eq_nsmul] using hNM v hv

end Squeeze

section Stabilizer

open scoped Pointwise

variable {R : Type*} (K : Type*) {V : Type*} [CommRing R] [CommRing K] [Algebra R K]
  [AddCommGroup V] [Module R V] [Module K V] [IsScalarTower R K V]

section Free

variable (L : Submodule R V) [L.IsFullLattice K] [Module.Free R L]

/-- **The stabilizer of a free full lattice is its automorphism group.** A `K`-linear
automorphism of `V` with `g L = L` restricts to an `R`-linear automorphism of `L`, and every
`R`-linear automorphism of `L` extends uniquely to `V` (`LinearEquiv.extendOfIsFullLattice`). -/
noncomputable def stabilizerMulEquiv :
    MulAction.stabilizer (V ≃ₗ[K] V) (L : Set V) ≃* (L ≃ₗ[R] L) where
  toFun g := ((g : V ≃ₗ[K] V).restrictScalars R).ofSubmodules L L
    (SetLike.coe_injective (by
      -- The image of `L` under `g` is the pointwise translate `g • L`, which is `L`.
      have h := MulAction.mem_stabilizer_iff.mp g.property
      simp only [← Set.image_smul, LinearEquiv.smul_def] at h
      simpa only [Submodule.map_coe, LinearEquiv.coe_coe, LinearEquiv.restrictScalars_apply]
        using h))
  invFun e := ⟨LinearEquiv.extendOfIsFullLattice (K := K) e, by
    -- The extension maps `L` onto `L`, and its image of `L` is its pointwise translate of `L`.
    rw [MulAction.mem_stabilizer_iff, ← Set.image_smul]
    have h := congrArg SetLike.coe (LinearEquiv.extendOfIsFullLattice_map (K := K) e)
    simpa only [Submodule.map_coe, LinearEquiv.coe_coe, LinearEquiv.restrictScalars_apply,
      LinearEquiv.smul_def] using h⟩
  left_inv g := Subtype.ext (LinearEquiv.eq_extendOfIsFullLattice _ _ fun _ => rfl).symm
  right_inv e := LinearEquiv.ext fun x => Subtype.ext (LinearEquiv.extendOfIsFullLattice_apply e x)
  map_mul' _ _ := LinearEquiv.ext fun _ => rfl

/-- The restriction of a stabilizing automorphism acts on the lattice as the automorphism. -/
@[simp]
theorem coe_stabilizerMulEquiv_apply (g : MulAction.stabilizer (V ≃ₗ[K] V) (L : Set V)) (x : L) :
    (L.stabilizerMulEquiv K g x : V) = (g : V ≃ₗ[K] V) x :=
  (rfl)

/-- The extension of a lattice automorphism acts on the lattice as the automorphism. -/
@[simp]
theorem stabilizerMulEquiv_symm_apply_coe (e : L ≃ₗ[R] L) (x : L) :
    (((L.stabilizerMulEquiv K).symm e : V ≃ₗ[K] V) x) = (e x : V) :=
  LinearEquiv.extendOfIsFullLattice_apply e x

end Free

variable {L : Submodule R V} [L.IsFullLattice K] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **The stabilizer of a lattice is `GL_n` of the coefficients.** Given an `R`-basis `b` of a
full lattice `L ⊆ V`, sending a `K`-linear automorphism with `g L = L` to the matrix in `b` of its
restriction to `L` is an isomorphism onto `GL ι R`. Its matrix in the ambient `K`-basis
`b.extendOfIsFullLattice K` is the image of that matrix in `K`
(`Module.Basis.map_stabilizerMulEquivGL_apply`). -/
noncomputable def _root_.Module.Basis.stabilizerMulEquivGL (b : Basis ι R L) :
    MulAction.stabilizer (V ≃ₗ[K] V) (L : Set V) ≃* GL ι R :=
  haveI := Module.Free.of_basis b
  (L.stabilizerMulEquiv K).trans b.toGL

variable {K}

/-- The matrix `b.stabilizerMulEquivGL K g` is the matrix in `b` of the restriction of `g` to the
lattice. -/
@[simp]
theorem _root_.Module.Basis.coe_stabilizerMulEquivGL_apply (b : Basis ι R L)
    (g : MulAction.stabilizer (V ≃ₗ[K] V) (L : Set V)) :
    letI := Module.Free.of_basis b
    (b.stabilizerMulEquivGL K g : Matrix ι ι R) =
      LinearMap.toMatrix b b (L.stabilizerMulEquiv K g : L →ₗ[R] L) :=
  letI := Module.Free.of_basis b
  b.coe_toGL (L.stabilizerMulEquiv K g)

/-- The matrix of a lattice-stabilizing automorphism in the ambient basis extended from a lattice
basis `b` is the image in `K` of its integral matrix `b.stabilizerMulEquivGL K g`. -/
theorem _root_.Module.Basis.map_stabilizerMulEquivGL_apply (b : Basis ι R L)
    (g : MulAction.stabilizer (V ≃ₗ[K] V) (L : Set V)) :
    (b.stabilizerMulEquivGL K g : Matrix ι ι R).map (algebraMap R K) =
      LinearMap.toMatrix (b.extendOfIsFullLattice K) (b.extendOfIsFullLattice K)
        (g : V ≃ₗ[K] V) := by
  ext i j
  simp [LinearMap.toMatrix_apply, ← Basis.extendOfIsFullLattice_repr_coe K]

/-- The automorphism of `V` attached to `u ∈ GL ι R` is the linear map with matrix `u`, read in
`K`, in the ambient basis extended from the lattice basis `b`. -/
theorem _root_.Module.Basis.stabilizerMulEquivGL_symm_apply (b : Basis ι R L) (u : GL ι R) :
    (((b.stabilizerMulEquivGL K).symm u : V ≃ₗ[K] V) : V →ₗ[K] V) =
      Matrix.toLin (b.extendOfIsFullLattice K) (b.extendOfIsFullLattice K)
        ((u : Matrix ι ι R).map (algebraMap R K)) := by
  have h := b.map_stabilizerMulEquivGL_apply ((b.stabilizerMulEquivGL K).symm u)
  rw [MulEquiv.apply_symm_apply] at h
  rw [h, Matrix.toLin_toMatrix]

/-- **A `K`-linear automorphism stabilizes a lattice exactly when its matrix is integral and
invertible over `R`.** In the ambient basis extended from an `R`-basis `b` of `L`, the matrix of
`g` is the image in `K` of a matrix in `GL ι R` if and only if `g L = L`. -/
theorem _root_.Module.Basis.mem_stabilizer_iff_exists_map_eq_toMatrix (b : Basis ι R L)
    (g : V ≃ₗ[K] V) :
    g ∈ MulAction.stabilizer (V ≃ₗ[K] V) (L : Set V) ↔
      ∃ u : GL ι R, (u : Matrix ι ι R).map (algebraMap R K) =
        LinearMap.toMatrix (b.extendOfIsFullLattice K) (b.extendOfIsFullLattice K) g := by
  refine ⟨fun hg => ⟨b.stabilizerMulEquivGL K ⟨g, hg⟩,
    b.map_stabilizerMulEquivGL_apply ⟨g, hg⟩⟩, fun ⟨u, hu⟩ => ?_⟩
  have h : (((b.stabilizerMulEquivGL K).symm u : V ≃ₗ[K] V) : V →ₗ[K] V) = g := by
    rw [b.stabilizerMulEquivGL_symm_apply, hu, Matrix.toLin_toMatrix]
  rw [← LinearEquiv.toLinearMap_inj.mp h]
  exact ((b.stabilizerMulEquivGL K).symm u).property

end Stabilizer

end Submodule

namespace TensorProduct

variable {R : Type u} {K : Type v} {M : Type w}

section CommRing

variable [CommRing R] [Field K] [Algebra R K] [IsFractionRing R K]

/-- The unit pure tensors form a full lattice in the scalar extension of a finite module. -/
instance isFullLattice_range_mk_one [AddCommMonoid M] [Module R M] [Module.Finite R M] :
    (LinearMap.range (TensorProduct.mk R K M 1)).IsFullLattice K where
  __ := Submodule.IsLattice.of_fg K (by
    rw [LinearMap.range_eq_map]
    exact Module.Finite.fg_top.map _)
  span_eq_top := by
    rw [eq_top_iff]
    rintro x -
    induction x using TensorProduct.inductionOn with
    | add x y hx hy => exact add_mem hx hy
    | tmul k m =>
      rw [tmul_eq_smul_one_tmul]
      exact Submodule.smul_mem _ k (Submodule.subset_span ⟨m, rfl⟩)

end CommRing

variable [CommRing R] [Field K] [Algebra R K] [IsFractionRing R K]
variable [AddCommGroup M] [Module R M] [Module.Free R M] [Module.Finite R M]

/-- Rationalizing the unit-tensor lattice recovers the scalar extension it sits in: base-changing
the unit-tensor equivalence and then rationalizing is the identity. -/
@[simp]
theorem rationalizationEquiv_baseChange_unitTmulEquiv (x : K ⊗[R] M) :
    Submodule.rationalizationEquiv (LinearMap.range (TensorProduct.mk R K M 1))
        (LinearEquiv.baseChange R K M _ (unitTmulEquiv R K M) x) = x := by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul k m =>
    rw [LinearEquiv.baseChange_tmul, Submodule.rationalizationEquiv_tmul,
      coe_unitTmulEquiv_apply]
    exact (tmul_eq_smul_one_tmul k m).symm

/-- The bundled form of `rationalizationEquiv_baseChange_unitTmulEquiv`. -/
theorem unitTmulEquiv_baseChange_trans_rationalizationEquiv :
    (LinearEquiv.baseChange R K M _ (unitTmulEquiv R K M)).trans
        (Submodule.rationalizationEquiv (LinearMap.range (TensorProduct.mk R K M 1))) =
      LinearEquiv.refl K (K ⊗[R] M) :=
  LinearEquiv.ext rationalizationEquiv_baseChange_unitTmulEquiv

end TensorProduct

namespace Submodule.IsLattice

universe u v w

variable {R : Type u} {K : Type v} {V' : Type w}
variable [CommRing R] [IsDomain R]
variable [Field K] [Algebra R K] [IsFractionRing R K]
variable [AddCommGroup V'] [Module R V'] [Module K V'] [IsScalarTower R K V']

variable (K) in
omit [IsDomain R] in
/-- Some nonzero multiple of every ambient vector lies in a submodule spanning the ambient space
over the fraction field `K`, in particular in a full lattice submodule. -/
theorem exists_ne_zero_smul_mem (S : Submodule R V') (hS : Submodule.span K (S : Set V') = ⊤)
    (v : V') : ∃ r : R, r ≠ 0 ∧ r • v ∈ S := by
  have := IsDomain.of_faithfulSMul R K
  have hv : v ∈ Submodule.span K (S : Set V') := by
    rw [hS]
    trivial
  obtain ⟨r, hr⟩ := multiple_mem_span_of_mem_localization_span (nonZeroDivisors R) K
    (S : Set V') v hv
  rw [Submodule.span_eq] at hr
  exact ⟨r, nonZeroDivisors.coe_ne_zero r, hr⟩

variable (K) in
/-- Every element of a scalar extension `T ⊗[R] V'` has a nonzero multiple in the base change of a
submodule spanning `V'` over the fraction field `K`. -/
theorem _root_.Submodule.exists_ne_zero_smul_mem_baseChange {T : Type*} [CommSemiring T]
    [Algebra R T] (S : Submodule R V') (hS : Submodule.span K (S : Set V') = ⊤) (z : T ⊗[R] V') :
    ∃ r : R, r ≠ 0 ∧ r • z ∈ S.baseChange T := by
  induction z using TensorProduct.inductionOn with
  | tmul t x =>
    obtain ⟨r, hr, hrx⟩ := exists_ne_zero_smul_mem K S hS x
    refine ⟨r, hr, ?_⟩
    rw [← TensorProduct.tmul_smul]
    exact Submodule.tmul_mem_baseChange_of_mem t hrx
  | add z₁ z₂ h₁ h₂ =>
    obtain ⟨r₁, hr₁, h₁⟩ := h₁
    obtain ⟨r₂, hr₂, h₂⟩ := h₂
    refine ⟨r₂ * r₁, mul_ne_zero hr₂ hr₁, ?_⟩
    rw [smul_add, mul_smul, mul_comm, mul_smul]
    exact add_mem ((S.baseChange T).smul_of_tower_mem r₂ h₁)
      ((S.baseChange T).smul_of_tower_mem r₁ h₂)

variable (K) in
omit [IsDomain R] in
/-- The `R`-finrank of a submodule spanning the ambient space over the fraction field `K`, in
particular of a full lattice, equals the `K`-finrank of the ambient space. -/
theorem _root_.Submodule.finrank_eq_finrank (N : Submodule R V')
    (hN : Submodule.span K (N : Set V') = ⊤) :
    Module.finrank R N = Module.finrank K V' := by
  have := IsDomain.of_faithfulSMul R K
  have := N.isLocalizedModule_subtype_of_span_eq_top (nonZeroDivisors R) hN
  rw [IsFractionRing.finrank_right_eq (R := R) (S := K) (N := V'),
    IsLocalizedModule.finrank_eq (nonZeroDivisors R) N.subtype le_rfl]

variable (K) in
omit [IsDomain R] in
/-- **Clearing denominators.** A single nonzero scalar multiplies a finitely generated submodule
into a submodule spanning the ambient space over `K`, such as a full lattice. -/
theorem exists_ne_zero_forall_smul_mem (S : Submodule R V')
    (hS : Submodule.span K (S : Set V') = ⊤) {M : Submodule R V'} (hM : M.FG) :
    ∃ r : R, r ≠ 0 ∧ ∀ x ∈ M, r • x ∈ S := by
  have := IsDomain.of_faithfulSMul R K
  obtain ⟨r, hr, h⟩ := hM.exists_smul_mem_of_le_span (F := K) (nonZeroDivisors R) (M := S)
    (by rw [hS]; exact fun _ _ ↦ Submodule.mem_top)
  exact ⟨r, nonZeroDivisors.ne_zero hr, h⟩

variable (K) in
/-- **Commensurability over a discrete valuation ring.** A power of the maximal ideal multiplies a
finitely generated submodule into a full lattice. -/
theorem _root_.Submodule.IsFullLattice.exists_maximalIdeal_pow_smul_le [IsDiscreteValuationRing R]
    (S : Submodule R V') [S.IsFullLattice K] {M : Submodule R V'} (hM : M.FG) :
    ∃ n : ℕ, IsLocalRing.maximalIdeal R ^ n • M ≤ S := by
  obtain ⟨r, hr0, hr⟩ :=
    exists_ne_zero_forall_smul_mem K S (IsFullLattice.span_eq_top (A := K) (M := S)) hM
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
  -- The ideal `(r)` is a power `(ϖ ^ n) = 𝔪 ^ n` of the maximal ideal.
  obtain ⟨n, hn⟩ := IsDiscreteValuationRing.ideal_eq_span_pow_irreducible
    (Ideal.span_singleton_eq_bot.not.mpr hr0) hϖ
  have hm : IsLocalRing.maximalIdeal R ^ n = Ideal.span {r} := by
    rw [hϖ.maximalIdeal_eq, Ideal.span_singleton_pow, hn]
  refine ⟨n, Submodule.smul_le.mpr fun s hs x hx ↦ ?_⟩
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp (hm ▸ hs)
  rw [mul_smul]
  exact S.smul_mem c (hr x hx)

end Submodule.IsLattice
