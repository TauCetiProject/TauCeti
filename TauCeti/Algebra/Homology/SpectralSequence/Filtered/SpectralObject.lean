/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.HomotopyCategory.ShortExact
public import Mathlib.Algebra.Homology.HomotopyCategory.SpectralObject
public import Mathlib.Algebra.Homology.SpectralObject.FirstPage
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.CategoryTheory.Subobject.Lattice

/-!
# The spectral object and the spectral sequence of a filtered complex

A functor `F : ι ⥤ CochainComplex C ℤ` to cochain complexes in an abelian category `C` gives a
spectral object `CochainComplex.spectralObject F` in `C` indexed by `ι`: to `f : i ⟶ j` and
`n : ℤ` it attaches the `n`th cohomology of the mapping cone of `F.map f`, and its connecting
maps are those of the distinguished triangles of mapping cones in the homotopy category. When
`F.map f` is a monomorphism, this cohomology is that of the cokernel of `F.map f`
(`CochainComplex.spectralObjectHIsoCokernel`). An increasing filtration `ℤ → Subobject K` of a
cochain complex `K`, extended by `⊥` and `⊤`, is such a functor indexed by `EInt`
(`CochainComplex.filtrationFunctor`), whose transition maps are monomorphisms.

The spectral sequence of a functor indexed by `EInt` is Mathlib's spectral sequence of a spectral
object, for the recipe `coreE₂Cohomological`
(`CochainComplex.spectralSequence`): its first page, numbered `2` there, has at `(p, q)` the
cohomology `H^{p+q}(F_{q+1}/F_q)` of a graded piece of the filtration
(`CochainComplex.spectralSequenceFirstPageXIso`).

## Main definitions

* `CochainComplex.spectralObject F`: the spectral object of `F : ι ⥤ CochainComplex C ℤ`.
* `CochainComplex.filtrationFunctor F hF`: the functor `EInt ⥤ CochainComplex C ℤ` of an
  increasing filtration `F : ℤ → Subobject K`.
* `CochainComplex.spectralSequence F`: the spectral sequence of `F : EInt ⥤ CochainComplex C ℤ`.

## Main results

* `CochainComplex.spectralObjectHIso`: `H^n(f)` is the cohomology of the mapping cone of
  `F.map f`.
* `CochainComplex.spectralObjectHIsoCokernel`: for a monomorphism `F.map f`, `H^n(f)` is the
  cohomology of the cokernel of `F.map f`.
* `CochainComplex.spectralSequenceFirstPageXIso`: the first page is `H^{p+q}(F_{q+1}/F_q)`.

## References

* J.-L. Verdier, *Des catégories dérivées des catégories abéliennes*, II.4.
* J. McCleary, *A User's Guide to Spectral Sequences*, Theorem 2.6.
-/

public section

open CategoryTheory Limits ComposableArrows HomotopyCategory

namespace CochainComplex

variable {C : Type*} [Category* C] [Abelian C]

section SpectralObject

variable {ι : Type*} [Category* ι] (F : ι ⥤ CochainComplex C ℤ)

/-- The spectral object of a functor `F : ι ⥤ CochainComplex C ℤ`: to `f : i ⟶ j` and `n : ℤ` it
attaches the `n`th cohomology of the mapping cone of `F.map f`, and its connecting maps are those
of the distinguished triangles of mapping cones. -/
noncomputable def spectralObject : Abelian.SpectralObject C ι :=
  ((spectralObjectMappingCone C).precomp F).mapHomologicalFunctor
    (homologyFunctor C (ComplexShape.up ℤ) 0)

/-- The objects `H^n(f)` of the spectral object of `F` are the cohomology of the mapping cones of
the maps `F.map f`. -/
noncomputable def spectralObjectHIso {i j : ι} (f : i ⟶ j) (n : ℤ) :
    ((spectralObject F).H n).obj (mk₁ f) ≅ (mappingCone (F.map f)).homology n :=
  (homologyFunctorFactors C (ComplexShape.up ℤ) n).app (mappingCone (F.map f))

/-- The short exact sequence `F i ⟶ F j ⟶ cokernel (F.map f)` of a monomorphism `F.map f`. -/
noncomputable abbrev cokernelShortComplex {i j : ι} (f : i ⟶ j) :
    ShortComplex (CochainComplex C ℤ) :=
  ShortComplex.mk (F.map f) (cokernel.π (F.map f)) (cokernel.condition _)

lemma cokernelShortComplex_shortExact {i j : ι} (f : i ⟶ j) [Mono (F.map f)] :
    (cokernelShortComplex F f).ShortExact :=
  ShortComplex.ShortExact.mk' (ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel _))
    inferInstance inferInstance

/-- When `F.map f` is a monomorphism, `H^n(f)` is the `n`th cohomology of the cokernel of
`F.map f`. -/
noncomputable def spectralObjectHIsoCokernel {i j : ι} (f : i ⟶ j) [Mono (F.map f)] (n : ℤ) :
    ((spectralObject F).H n).obj (mk₁ f) ≅ (cokernel (F.map f)).homology n :=
  have := mappingCone.quasiIso_descShortComplex (cokernelShortComplex_shortExact F f)
  spectralObjectHIso F f n ≪≫
    asIso (HomologicalComplex.homologyMap
      (mappingCone.descShortComplex (cokernelShortComplex F f)) n)

end SpectralObject

section Filtration

variable {K : CochainComplex C ℤ} (F : ℤ → Subobject K) (hF : Monotone F)

/-- An increasing filtration `F : ℤ → Subobject K` extended to `EInt`, by `⊥` at `⊥` and `⊤` at
`⊤`. -/
@[expose] noncomputable def filtrationEInt : EInt → Subobject K :=
  WithBotTop.rec ⊥ F ⊤

@[simp]
lemma filtrationEInt_bot : filtrationEInt F ⊥ = ⊥ := rfl

@[simp]
lemma filtrationEInt_coe (n : ℤ) : filtrationEInt F n = F n := rfl

@[simp]
lemma filtrationEInt_top : filtrationEInt F ⊤ = ⊤ := rfl

include hF in
lemma monotone_filtrationEInt : Monotone (filtrationEInt F) := by
  intro a b hab
  induction a using WithBotTop.rec with
  | bot => simp
  | top =>
    induction b using WithBotTop.rec with
    | top => simp
    | bot => simp at hab
    | coe b => exact absurd hab (by simp)
  | coe a =>
    induction b using WithBotTop.rec with
    | bot => exact absurd hab (by simp)
    | top => simp
    | coe b => simpa using hF (WithBotTop.coe_le_coe.mp hab)

/-- The functor `EInt ⥤ CochainComplex C ℤ` of an increasing filtration `F : ℤ → Subobject K`:
it sends `n : ℤ` to the subcomplex `F n`, `⊥` to the zero subcomplex and `⊤` to `K`. -/
noncomputable def filtrationFunctor : EInt ⥤ CochainComplex C ℤ :=
  (monotone_filtrationEInt F hF).functor ⋙ Subobject.underlying

instance {a b : EInt} (f : a ⟶ b) : Mono ((filtrationFunctor F hF).map f) :=
  inferInstanceAs (Mono (Subobject.ofLE _ _
    (monotone_filtrationEInt F hF (leOfHom f))))

end Filtration

section SpectralSequence

variable (F : EInt ⥤ CochainComplex C ℤ)

/-- The spectral sequence of a functor `F : EInt ⥤ CochainComplex C ℤ`, starting on page `2`
(the first page in Mathlib's numbering for `coreE₂Cohomological`). -/
noncomputable abbrev spectralSequence :=
  (spectralObject F).spectralSequence Abelian.SpectralObject.coreE₂Cohomological

/-- The objects on the first page of the spectral sequence of `F`: at `(p, q)`, the
`(p + q)`th cohomology of the mapping cone of `F_q ⟶ F_{q+1}`. -/
noncomputable def spectralSequenceFirstPageXIso (p q : ℤ) :
    ((spectralSequence F).page 2).X (p, q) ≅
      (mappingCone (F.map (homOfLE (show (q : EInt) ≤ (q + 1 : ℤ) by simp)))).homology
        (p + q) :=
  (spectralObject F).spectralSequenceFirstPageXIso _ (p, q) q (q + 1 : ℤ) rfl rfl (p + q) rfl ≪≫
    spectralObjectHIso F _ _

/-- The objects on the first page of the spectral sequence of `F` when the transition maps of
`F` are monomorphisms: at `(p, q)`, the `(p + q)`th cohomology of the graded piece
`F_{q+1}/F_q`. -/
noncomputable def spectralSequenceFirstPageXIsoCokernel (p q : ℤ)
    [Mono (F.map (homOfLE (show (q : EInt) ≤ (q + 1 : ℤ) by simp)))] :
    ((spectralSequence F).page 2).X (p, q) ≅
      (cokernel (F.map (homOfLE (show (q : EInt) ≤ (q + 1 : ℤ) by simp)))).homology (p + q) :=
  (spectralObject F).spectralSequenceFirstPageXIso _ (p, q) q (q + 1 : ℤ) rfl rfl (p + q) rfl ≪≫
    spectralObjectHIsoCokernel F _ _

end SpectralSequence

end CochainComplex
