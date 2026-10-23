/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.Coalgebra.Comodule.Finite.Abelian
public import TauCeti.Algebra.Coalgebra.Comodule.LinearlyReductive
public import TauCeti.Algebra.Homology.ShortComplex.ShortExact

/-!
# Linear reductivity and split exact sequences

A finite-dimensional comodule is completely reducible if and only if every monomorphism
into it splits. Consequently a coalgebra is linearly reductive if and only if every short
exact sequence of finite-dimensional comodules splits. For coordinate Hopf algebras, this
identifies the invariant-complement definition of linear reductivity with its categorical
formulation in the rational representation category.

No Hopf algebra structure or finite-dimensionality of the coalgebra is required. The monomorphism
criterion and the middle-term splitting theorem hold more generally for finite comodules over a
flat coalgebra over a Noetherian commutative ring.

## References

* W. C. Waterhouse, *Introduction to Affine Group Schemes*, Section 3.2.
-/

public section

open CategoryTheory CategoryTheory.Limits

namespace TauCeti

universe u v w

section

variable {k : Type u} [CommRing k]
variable {C : Type v} [AddCommMonoid C] [Module k C] [Coalgebra k C]

namespace FGComoduleCat

variable [IsNoetherianRing k] [Module.Flat k C]

/-- A finite comodule over a flat coalgebra over a Noetherian ring is completely reducible exactly
when every monomorphism into it admits a retraction. -/
theorem isCompletelyReducible_iff_forall_isSplitMono (M : FGComoduleCat.{u, v, w} k C) :
    Comodule.IsCompletelyReducible k C M ↔
      ∀ (N : FGComoduleCat.{u, v, w} k C) (f : N ⟶ M), Mono f → IsSplitMono f := by
  constructor
  · intro hM N f hf
    let W := f.hom.range
    let : Module.Finite k W := W.finite
    obtain ⟨P, hP, hfix⟩ :=
      (Comodule.isCompletelyReducible_iff_forall_exists_hom.mp hM) W
    let e : N ⟶ of (R := k) (C := C) W :=
      ofHom (f.hom.codRestrict W (Comodule.Hom.mem_range_self f.hom))
    let i : of (R := k) (C := C) W ⟶ M := ofHom W.subtype
    have hei : e ≫ i = f := by
      apply ObjectProperty.hom_ext
      exact Comodule.Hom.subtype_comp_codRestrict _ _ _
    have : Mono e := mono_of_mono_fac hei
    have : Epi e := ConcreteCategory.epi_of_surjective e fun x ↦ by
      obtain ⟨y, hy⟩ := Comodule.Hom.mem_range.mp x.property
      refine ⟨y, Subtype.ext ?_⟩
      exact (Comodule.Hom.codRestrict_apply _ _ _ y).trans hy
    have : IsIso e := isIso_of_mono_of_epi e
    let p : M ⟶ of (R := k) (C := C) W := ofHom (P.codRestrict W hP)
    have hip : i ≫ p = 𝟙 _ := by
      apply ObjectProperty.hom_ext
      apply Comodule.Hom.ext
      intro x
      apply Subtype.ext
      exact (Comodule.Hom.codRestrict_apply P W hP (W.subtype x)).trans
        ((hfix (W.subtype x)
          (by simpa only [Subcomodule.subtype_apply] using x.property)).trans
            (Subcomodule.subtype_apply W x))
    exact IsSplitMono.mk' ⟨p ≫ inv e, by
      rw [← hei, Category.assoc, ← Category.assoc i, hip]
      simp⟩
  · intro hM
    apply Comodule.isCompletelyReducible_iff_forall_exists_hom.mpr
    intro W
    let : Module.Finite k W := W.finite
    let i : of (R := k) (C := C) W ⟶ M := ofHom W.subtype
    have hi : Mono i := ConcreteCategory.mono_of_injective i fun x y hxy ↦ by
      apply Subtype.ext
      have h : W.subtype x = W.subtype y := hxy
      simpa only [Subcomodule.subtype_apply] using h
    obtain ⟨r, hr⟩ := (hM _ i hi).exists_splitMono
    let r' : Comodule.Hom k C M W := r.hom
    refine ⟨W.subtype.comp r', ?_, ?_⟩
    · intro x
      simpa only [Comodule.Hom.comp_apply, Subcomodule.subtype_apply] using (r' x).property
    · intro x hx
      have h : r' (W.subtype ⟨x, hx⟩) = ⟨x, hx⟩ :=
        congrArg (fun g : of (R := k) (C := C) W ⟶
          of (R := k) (C := C) W ↦ (g.hom : Comodule.Hom k C W W) ⟨x, hx⟩) hr
      simpa only [Comodule.Hom.comp_apply, Subcomodule.subtype_apply] using
        congrArg Subtype.val h

/-- A short exact sequence with completely reducible middle comodule splits. -/
theorem _root_.CategoryTheory.ShortComplex.nonempty_splitting_of_isCompletelyReducible
    (S : ShortComplex (FGComoduleCat.{u, v, w} k C)) (hS : S.ShortExact)
    (hM : Comodule.IsCompletelyReducible k C S.X₂) : Nonempty S.Splitting := by
  obtain ⟨r, hr⟩ :=
    ((isCompletelyReducible_iff_forall_isSplitMono S.X₂).mp hM S.X₁ S.f hS.mono_f).exists_splitMono
  exact ⟨ShortComplex.Splitting.ofExactOfRetraction S hS.exact r hr hS.epi_g⟩

end FGComoduleCat

end

namespace Coalgebra

variable {k : Type u} [Field k]
variable {C : Type v} [AddCommMonoid C] [Module k C] [Coalgebra k C]

/-- Linear reductivity is equivalent to splitting every short exact sequence of
finite-dimensional comodules. It suffices to test comodules in the base field’s universe. -/
theorem isLinearlyReductive_iff_forall_nonempty_splitting :
    IsLinearlyReductive.{u, v, u} k C ↔
      ∀ S : ShortComplex (FGComoduleCat.{u, v, u} k C),
        S.ShortExact → Nonempty S.Splitting := by
  let : AddCommGroup C := Module.addCommMonoidToAddCommGroup k
  constructor
  · intro h S hS
    exact S.nonempty_splitting_of_isCompletelyReducible hS
      (IsLinearlyReductive.isCompletelyReducible k h)
  · intro h
    apply IsLinearlyReductive.of_forall_isCompletelyReducible
    intro V _ _ _ _
    apply (FGComoduleCat.isCompletelyReducible_iff_forall_isSplitMono
      (FGComoduleCat.of (R := k) (C := C) V)).mpr
    intro N f hf
    let : Mono f := hf
    obtain ⟨s⟩ := h (ShortComplex.cokernelSequence f) (cokernelSequence_shortExact f)
    exact s.isSplitMono_f

end Coalgebra

end TauCeti
