/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Representation.Embedding
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Quotient.Image.Basic
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Coinvariants.Quotient
public import TauCeti.Algebra.AlgebraicGroup.GeometricallyReduced.FaithfullyFlat
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Quotient.Kernel.Coinvariants

/-!
# Finite generation of Hopf subalgebras

Every finite subset of a commutative Hopf algebra over a field lies in the image of an
injective morphism from a finite-type commutative Hopf algebra. A finite-dimensional regular
subcomodule containing the subset gives a representation; the image of its coordinate
morphism supplies the finite-type algebra.

If a coordinate morphism lands in a Noetherian algebra, a finite-type part of its source
already detects its entire scheme-theoretic kernel. When the codomain is geometrically reduced
and finite type, the existing faithful-flatness theorem makes this finite-type approximation
surjective onto an injective morphism's source. Consequently every Hopf subalgebra of a
geometrically reduced finite-type commutative Hopf algebra is finite type. This supplies
finite generation of coordinate algebras for normal affine-group quotients.

The construction reuses `Comodule.coordinateBialgHom` and the finite-dimensional subcoalgebra
argument in `Comodule.exists_coordinateBialgHom_surjective`.

## References

* W. C. Waterhouse, *Introduction to Affine Group Schemes*, §§3.3 and 16.3.
* J. S. Milne, *Algebraic Groups* (2017), §4.a and §5.c.
-/

public section

open CategoryTheory

namespace CommHopfAlgCat

open TauCeti TauCeti.CommHopfAlgCat

universe u

noncomputable section

variable {k : Type u} [Field k]

/-- Every finite subset of a commutative Hopf algebra over a field lies in the image of an
injective coordinate morphism from a finite-type commutative Hopf algebra. No finite-generation
hypothesis on the ambient algebra is required. -/
theorem exists_finiteType_injective_range_contains
    (H : _root_.CommHopfAlgCat.{u} k) (s : Set H) (hs : s.Finite) :
    ∃ (L : _root_.CommHopfAlgCat.{u} k) (_ : Algebra.FiniteType k L)
      (i : L ⟶ H), Function.Injective i.hom ∧ s ⊆ i.hom.toAlgHom.range := by
  obtain ⟨D, hD, hsD⟩ :=
    Subcoalgebra.exists_finiteDimensional_subcoalgebra_of_setFinite (k := k) s hs
  let : Module.Finite k D.toSubmodule := hD
  let M := D.toRegularSubcomodule
  let : AddCommGroup M := Module.addCommMonoidToAddCommGroup k
  let : Module.Finite k M := D.toRegularSubcomodule_finite
  let b := Module.finBasis k M
  let f : _root_.CommHopfAlgCat.of k
      (GeneralLinear.coordinateHopfAlgebra k (Module.finrank k M)) ⟶ H :=
    _root_.CommHopfAlgCat.ofHom (Comodule.coordinateBialgHom (H := H) b)
  refine ⟨image f, inferInstance, imageι f, imageι_injective f, ?_⟩
  intro x hx
  have hcoeff : x ∈ Comodule.matrixCoefficientSubalgebra (R := k) (C := H) (M := M) :=
    Subcoalgebra.le_matrixCoefficientSubalgebra_toRegularSubcomodule D (hsD hx)
  obtain ⟨y, hy⟩ := Comodule.matrixCoefficientSubalgebra_le_coordinateBialgHom_range b hcoeff
  exact ⟨(mkImage f).hom y, (imageι_mkImage_apply f y).trans hy⟩

/-- A finite-type part of the target of a homomorphism from an affine group with Noetherian
coordinate ring detects the entire scheme-theoretic kernel. In coordinates, precomposing with
an injective morphism from a finite-type Hopf algebra leaves `kernelHopfIdeal` unchanged. -/
theorem exists_finiteType_injective_kernelHopfIdeal_eq
    {H K : _root_.CommHopfAlgCat.{u} k} [IsNoetherianRing K] (f : H ⟶ K) :
    ∃ (L : _root_.CommHopfAlgCat.{u} k) (_ : Algebra.FiniteType k L)
      (i : L ⟶ H), Function.Injective i.hom ∧
        kernelHopfIdeal (i ≫ f) = kernelHopfIdeal f := by
  let s : Set K := f.hom '' (HopfIdeal.augmentation k H : Set H)
  obtain ⟨t, ht, hspan⟩ :=
    (Submodule.fg_span_iff_fg_span_finset_subset (R := K) s).mp
      (IsNoetherian.noetherian (Submodule.span K s))
  obtain ⟨s₀, hs₀, hs₀fin, himage⟩ := t.finite_toSet.exists_subset_finite_image_eq ht
  obtain ⟨L, hL, i, hi, hs₀i⟩ := exists_finiteType_injective_range_contains H s₀ hs₀fin
  refine ⟨L, hL, i, hi, le_antisymm (kernelHopfIdeal_comp_le i f) ?_⟩
  have hkernel : (kernelHopfIdeal f).toIdeal = Ideal.span s := by
    rw [kernelHopfIdeal_toIdeal]
    -- `Ideal.map` is defined as the ideal span of the image of its carrier.
    rfl
  have hspanIdeal : Ideal.span s = Ideal.span (t : Set K) := hspan
  rw [← HopfIdeal.toIdeal_le_toIdeal, hkernel, hspanIdeal, ← himage, Ideal.span_le]
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨z, hz⟩ := hs₀i hx
  have hiz : i.hom z = x := hz
  have hc : Coalgebra.counit (R := k) z = 0 := by
    have hx₀ := (HopfIdeal.mem_augmentation k H).mp (hs₀ hx)
    rw [← hiz, CoalgHomClass.counit_comp_apply] at hx₀
    exact hx₀
  have hzmem := mem_kernelHopfIdeal_of_mem_augmentation (i ≫ f) hc
  exact HopfIdeal.mem_toIdeal.mpr (by
    simpa only [_root_.CommHopfAlgCat.hom_comp, BialgHom.comp_apply, hiz] using hzmem)

/-- A commutative Hopf algebra that embeds in a geometrically reduced finite-type commutative
Hopf algebra over a field is itself finite type. -/
theorem finiteType_of_injective
    {H K : _root_.CommHopfAlgCat.{u} k} [Algebra.FiniteType k K]
    [Algebra.IsGeometricallyReduced k K] (f : H ⟶ K)
    (hf : Function.Injective f.hom) : Algebra.FiniteType k H := by
  let : IsNoetherianRing K := Algebra.FiniteType.isNoetherianRing k K
  obtain ⟨L, hL, i, hi, hker⟩ := exists_finiteType_injective_kernelHopfIdeal_eq f
  let : Algebra.FiniteType k L := hL
  have hcomp : Function.Injective (i ≫ f).hom := hf.comp hi
  let : Algebra.IsGeometricallyReduced k L :=
    Algebra.IsGeometricallyReduced.of_injective (i ≫ f).hom.toAlgHom hcomp
  have hflat := (faithfullyFlat_iff_injective_of_isGeometricallyReduced (i ≫ f)).mpr hcomp
  have hcoinv := coinvariants_kernelHopfIdeal_eq_range (i ≫ f) hflat
  rw [hker] at hcoinv
  have hi_surjective : Function.Surjective i.hom := by
    intro x
    have hx := (HopfIdeal.forall_hom_mem_coinvariants_iff f).mpr le_rfl x
    rw [hcoinv] at hx
    obtain ⟨y, hy⟩ := hx
    refine ⟨y, hf ?_⟩
    exact hy
  exact Algebra.FiniteType.of_surjective i.hom.toAlgHom hi_surjective

end

end CommHopfAlgCat
