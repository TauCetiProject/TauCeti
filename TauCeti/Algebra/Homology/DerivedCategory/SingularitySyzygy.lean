/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Abelian.Injective.Dimension
public import TauCeti.Algebra.Homology.DerivedCategory.Perfect
public import TauCeti.Algebra.Homology.HomologicalComplex.Basic
public import TauCeti.CategoryTheory.Triangulated.FullSubcategory

/-!
# Objects of the singularity category are shifted syzygies

Let `C` be an abelian category with enough projectives. Every object of the singularity category
`D_sg(C) = Dᵇ(C) / Perf(C)` is isomorphic to an object `M` of `C` placed in some degree. Moreover,
for every `d`, the object `M` can be chosen to be a `d`-th syzygy: it has no higher extensions
`Ext^{i+1}(M, Y)` into objects `Y` of injective dimension at most `d`.

Represent an object of `Dᵇ(C)` by a bounded above complex `K` of projective objects, exact below
some degree `a`. For `m` far below `a`, the canonical truncation `K.truncGE m` is quasi-isomorphic
to `K`. Its terms are projective except in degree `m`, where it is `K.opcycles m`, so it is an
extension of `K.opcycles m` placed in degree `m` by a bounded complex of projectives, which is
perfect. Hence `K ≅ (K.opcycles m)[-m]` in the singularity category. Since `K` is exact around
`m`, `K.opcycles m` is the module of cycles `Zᵐ⁺¹`, and the short exact sequences
`0 ⟶ Zʲ ⟶ Kʲ ⟶ Zʲ⁺¹ ⟶ 0` with projective middle terms shift `Ext^{i+1}(Zᵐ⁺¹, Y)` into
`Ext^{i+1+d}(Zᵐ⁺¹⁺ᵈ, Y)`, which vanishes when `Y` has injective dimension at most `d`.

## Main results

* `HomologicalComplex.isIso_opcyclesToCycles`: the opcycles in degree `i` are the cycles in degree
  `j` when the complex is exact in both degrees.
* `CochainComplex.ext_cycles_eq_zero_of_hasInjectiveDimensionLE`: for a complex of projectives
  exact in degrees `j + 1, …, j + d`, the cycles in degree `j` have no higher extensions into
  objects of injective dimension at most `d`.
* `TauCeti.SingularityCategory.exists_iso_Q_obj_singleFunctor_obj`: every object of the
  singularity category is isomorphic to a `d`-th syzygy placed in some degree.

## References

* Ragnar-Olaf Buchweitz, *Maximal Cohen–Macaulay Modules and Tate Cohomology*, Mathematical
  Surveys and Monographs **262**, American Mathematical Society (2021), Section 4.4.
-/

public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian CategoryTheory.Pretriangulated
  ZeroObject

universe w' w v u

namespace HomologicalComplex

variable {C : Type u} [Category.{v} C] [Abelian C] {ι : Type*} {c : ComplexShape ι}
  (K : HomologicalComplex C c)

/-- If a complex is exact in degrees `i` and `j`, with `c.Rel i j`, the map from the opcycles in
degree `i` to the cycles in degree `j` is an isomorphism, by the exact sequence
`Hⁱ ⟶ opcyclesⁱ ⟶ Zʲ ⟶ Hʲ`. -/
lemma isIso_opcyclesToCycles {i j : ι} (hij : c.Rel i j) (hi : K.ExactAt i) (hj : K.ExactAt j) :
    IsIso (K.opcyclesToCycles i j) := by
  have h := HomologySequence.composableArrows₃_exact K i j hij
  have : Mono (K.opcyclesToCycles i j) :=
    (h.exact 0).mono_g (hi.isZero_homology.eq_of_src _ _)
  have : Epi (K.opcyclesToCycles i j) :=
    (h.exact 1).epi_f (hj.isZero_homology.eq_of_tgt _ _)
  exact isIso_of_mono_of_epi _

end HomologicalComplex

namespace CochainComplex

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C] {K : CochainComplex C ℤ}
  (hK : ∀ n, Projective (K.X n)) {Y : C}
include hK

/-- **One dimension shift along the cycles**: if `K` is exact in degree `j + 1` and its terms are
projective, then `Ext^{i+1}(Zʲ, Y)` embeds into `Ext^{i+2}(Zʲ⁺¹, Y)`. -/
private lemma ext_cycles_eq_zero_of_succ (j : ℤ) (hj : K.ExactAt (j + 1)) (i : ℕ)
    (h : ∀ e : Ext.{w} (K.cycles (j + 1)) Y (i + 2), e = 0) (e : Ext.{w} (K.cycles j) Y (i + 1)) :
    e = 0 := by
  have hS : (ShortComplex.mk (K.iCycles j) (K.toCycles j (j + 1))
      (K.iCycles_toCycles j (j + 1))).ShortExact :=
    K.cyclesShortComplex_def j (j + 1) ▸ K.cyclesShortComplex_shortExact j (j + 1) rfl hj
  obtain ⟨x, rfl⟩ := Ext.contravariant_sequence_exact₁ hS Y e (n₁ := i + 2) (by lia) (h _)
  have := hK j
  rw [Ext.eq_zero_of_projective x, Ext.comp_zero]

/-- **Dimension shifting along the cycles**: if `K` is exact in degrees `j + 1, …, j + k` and its
terms are projective, then `Ext^{i+1}(Zʲ, Y)` vanishes whenever `Ext^{i+k+1}(Zʲ⁺ᵏ, Y)` does. -/
private lemma ext_cycles_eq_zero_of_add (k : ℕ) :
    ∀ (j j' : ℤ), j' = j + k → (∀ l : ℕ, l < k → K.ExactAt (j + l + 1)) → ∀ i : ℕ,
      (∀ n, n = i + k + 1 → ∀ e : Ext.{w} (K.cycles j') Y n, e = 0) →
        ∀ e : Ext.{w} (K.cycles j) Y (i + 1), e = 0 := by
  induction k with
  | zero =>
    intro j j' hj' _ i h
    obtain rfl : j' = j := by simpa using hj'
    exact h _ rfl
  | succ k ih =>
    intro j j' hj' hK' i h
    refine ext_cycles_eq_zero_of_succ hK j (by simpa using hK' 0 (by lia)) i
      (ih (j + 1) j' (by rw [hj']; push_cast; ring) (fun l hl ↦ ?_) (i + 1)
        (fun n hn ↦ h n (by lia)))
    have := hK' (l + 1) (by lia)
    push_cast at this
    rwa [show j + (l + 1 : ℤ) + 1 = j + 1 + l + 1 by ring] at this

/-- **Cycles of an exact range have no higher extensions into objects of small injective
dimension**: if `K` has projective terms and is exact in degrees `j + 1, …, j + d`, then
`Ext^{i+1}(Zʲ, Y) = 0` for every object `Y` of injective dimension at most `d`. -/
theorem ext_cycles_eq_zero_of_hasInjectiveDimensionLE (d : ℕ) [HasInjectiveDimensionLE Y d]
    (j : ℤ) (hj : ∀ l : ℕ, l < d → K.ExactAt (j + l + 1)) (i : ℕ)
    (e : Ext.{w} (K.cycles j) Y (i + 1)) : e = 0 :=
  ext_cycles_eq_zero_of_add hK d j (j + d) rfl hj i
    (fun n hn e ↦ e.eq_zero_of_hasInjectiveDimensionLT (d + 1) (by lia)) e

end CochainComplex

namespace TauCeti.SingularityCategory

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]

open _root_.DerivedCategory in
/-- **Objects of the singularity category are shifted syzygies**: in an abelian category with
enough projectives, every object of the singularity category is isomorphic to an object `M` of `C`
placed in some degree, where `M` can be chosen with `Ext^{i+1}(M, Y) = 0` for all objects `Y` of
injective dimension at most a given `d`. -/
theorem exists_iso_Q_obj_singleFunctor_obj [EnoughProjectives C] [HasExt.{w'} C]
    (X : _root_.DerivedCategory.Bounded C) (d : ℕ) :
    ∃ (M : C) (n : ℤ), (∀ (Y : C) [HasInjectiveDimensionLE Y d] (i : ℕ)
        (e : Ext.{w'} M Y (i + 1)), e = 0) ∧
      Nonempty ((Q C).obj X ≅ (Q C).obj ((DerivedCategory.Bounded.singleFunctor C n).obj M)) := by
  obtain ⟨K, b, _, hK, ⟨e⟩⟩ :=
    (boundedAboveProjective_iff _).1 (boundedAboveProjective_of_bounded X)
  obtain ⟨a, ha⟩ := X.property.1
  have : TStructure.t.IsGE (_root_.DerivedCategory.Bounded.ι.obj X) a := ha
  have : K.IsGE a := (isGE_Q_obj_iff K a).1 (TStructure.t.isGE_of_iso e.symm a)
  -- Truncate `K` in a degree `m` such that `K` is exact in degrees `m, …, m + d + 1`.
  obtain ⟨m, hm⟩ : ∃ m : ℤ, m = a - d - 2 := ⟨_, rfl⟩
  have : K.IsGE m := K.isGE_of_ge m a (by lia)
  have : QuasiIso (K.πTruncGE m) := (K.quasiIso_πTruncGE_iff m).2 inferInstance
  let T := K.truncGE m
  -- The projection of `T` onto its lowest term, placed in degree `m`, and its kernel.
  let π : T ⟶ (HomologicalComplex.single C (.up ℤ) m).obj (T.X m) :=
    HomologicalComplex.mkHomToSingle (𝟙 _) fun i hi ↦
      (T.isZero_of_isStrictlyGE m i (by simp at hi; lia)).eq_of_src _ _
  have : Epi π := HomologicalComplex.epi_of_epi_f _ fun i ↦ by
    by_cases hi : i = m
    · rw [hi, show π.f m = 𝟙 _ ≫ (HomologicalComplex.singleObjXSelf (.up ℤ) m (T.X m)).inv from
        HomologicalComplex.mkHomToSingle_f _ _]
      infer_instance
    · exact ⟨fun g h _ ↦ (HomologicalComplex.isZero_single_obj_X _ _ _ _ hi).eq_of_src g h⟩
  let S := ShortComplex.mk (kernel.ι π) π (kernel.condition π)
  have hS : S.ShortExact := .mk' (S.exact_of_f_is_kernel (kernelIsKernel π)) inferInstance
    inferInstance
  -- The kernel of `π` agrees with `T` above degree `m` and vanishes elsewhere.
  have hker (i : ℤ) : (kernel π).X i ≅ kernel (π.f i) :=
    PreservesKernel.iso (HomologicalComplex.eval C (.up ℤ) i) π
  have hkerT (i : ℤ) (hi : i ≠ m) : (kernel π).X i ≅ T.X i :=
    hker i ≪≫ kernelIsoOfEq ((HomologicalComplex.isZero_single_obj_X _ _ _ _ hi).eq_of_tgt _ 0) ≪≫
      kernelZeroIsoSource
  have hkerm : IsZero ((kernel π).X m) := by
    have : Mono (π.f m) := by
      rw [show π.f m = 𝟙 _ ≫ (HomologicalComplex.singleObjXSelf (.up ℤ) m (T.X m)).inv from
        HomologicalComplex.mkHomToSingle_f _ _]
      infer_instance
    exact (isZero_kernel_of_mono (π.f m)).of_iso (hker m)
  have hlow (i : ℤ) (hi : i ≤ m) : IsZero ((kernel π).X i) := by
    obtain hi | rfl := hi.lt_or_eq
    · exact (T.isZero_of_isStrictlyGE m i hi).of_iso (hkerT i hi.ne)
    · exact hkerm
  have hhigh (i : ℤ) (hi : b < i) : IsZero ((kernel π).X i) := by
    obtain hm' | hm' := le_or_gt i m
    · exact hlow i hm'
    · exact (K.isZero_of_isStrictlyLE b i hi).of_iso (hkerT i hm'.ne' ≪≫ K.truncGEXIso m i hm')
  have hproj (i : ℤ) : Projective ((kernel π).X i) := by
    by_cases hi : m < i
    · exact Projective.of_iso (hkerT i hi.ne' ≪≫ K.truncGEXIso m i hi).symm inferInstance
    · exact (hlow i (not_lt.1 hi)).projective
  have : (kernel π).IsStrictlyGE m := by
    rw [CochainComplex.isStrictlyGE_iff]
    exact fun i hi ↦ hlow i hi.le
  have : (kernel π).IsStrictlyLE b := by
    rw [CochainComplex.isStrictlyLE_iff]
    exact hhigh
  -- The kernel is perfect, being a bounded complex of projectives.
  let K' : CochainComplex.Bounded C :=
    ⟨kernel π, (CochainComplex.bounded_iff _ _).2 ⟨m, b, ‹_›, ‹_›⟩⟩
  let eK : _root_.DerivedCategory.Bounded.ι.obj ((TauCeti.DerivedCategory.Bounded.Qh C).obj
      ((TauCeti.HomotopyCategory.Bounded.quotient C).obj K')) ≅
        _root_.DerivedCategory.Q.obj (kernel π) :=
    (TauCeti.DerivedCategory.Bounded.QhCompιIsoιCompQh C).app _ ≪≫
      Qh.mapIso (eqToIso (TauCeti.HomotopyCategory.Bounded.quotient_obj_obj C K')) ≪≫
      (quotientCompQhIso C).app (kernel π)
  let eT : _root_.DerivedCategory.Q.obj T ≅ _root_.DerivedCategory.Bounded.ι.obj X :=
    (asIso (_root_.DerivedCategory.Q.map (K.πTruncGE m))).symm ≪≫ e
  -- The triangle of `0 ⟶ ker π ⟶ T ⟶ T.X m[-m] ⟶ 0`, in the bounded derived category.
  obtain ⟨T', hT', ⟨φ⟩⟩ := ObjectProperty.exists_distTriang_mapTriangle_iso _
    (triangleOfSES_distinguished hS)
    (TStructure.t.bounded.prop_of_iso eK ((TauCeti.DerivedCategory.Bounded.Qh C).obj _).property)
    (TStructure.t.bounded.prop_of_iso eT.symm X.property)
  have h₁ : TauCeti.DerivedCategory.Bounded.perfect C T'.obj₁ :=
    (TauCeti.DerivedCategory.Bounded.perfect C).prop_of_iso
      ((ObjectProperty.fullyFaithfulι _).preimageIso (eK ≪≫ (Triangle.π₁.mapIso φ).symm))
      (TauCeti.DerivedCategory.Bounded.perfect_Qh_obj_quotient_obj C K' hproj)
  have := Localization.inverts (Q C) _ _ (ObjectProperty.trW.mk' _ hT' h₁)
  let eM : T.X m ≅ K.cycles (m + 1) := K.truncGEXIsoOpcycles m ≪≫
    (have := K.isIso_opcyclesToCycles (show (ComplexShape.up ℤ).Rel m (m + 1) from rfl)
      (K.exactAt_of_isGE a m (by lia)) (K.exactAt_of_isGE a (m + 1) (by lia))
    asIso (K.opcyclesToCycles m (m + 1)))
  let eX : T'.obj₂ ≅ X := (ObjectProperty.fullyFaithfulι _).preimageIso (Triangle.π₂.mapIso φ ≪≫ eT)
  let eS : T'.obj₃ ≅ (DerivedCategory.Bounded.singleFunctor C m).obj (K.cycles (m + 1)) :=
    (ObjectProperty.fullyFaithfulι _).preimageIso (Triangle.π₃.mapIso φ ≪≫
      _root_.DerivedCategory.Q.mapIso ((HomologicalComplex.single C (.up ℤ) m).mapIso eM) ≪≫
      ((singleFunctorIsoCompQ C m).app (K.cycles (m + 1))).symm)
  refine ⟨K.cycles (m + 1), m, fun Y _ i e' ↦ ?_,
    ⟨(Q C).mapIso eX.symm ≪≫ asIso ((Q C).map T'.mor₂) ≪≫ (Q C).mapIso eS⟩⟩
  exact CochainComplex.ext_cycles_eq_zero_of_hasInjectiveDimensionLE hK d (m + 1)
    (fun l hl ↦ K.exactAt_of_isGE a _ (by lia)) i e'

end TauCeti.SingularityCategory
