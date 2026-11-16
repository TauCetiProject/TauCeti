/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
public import Mathlib.Algebra.Homology.HomologicalComplexBiprod
public import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLEGT
public import TauCeti.Algebra.Homology.DerivedCategory.Plus.Functor
public import TauCeti.Algebra.Homology.HomologicalComplex.Acyclic
public import TauCeti.Algebra.Homology.HomologySequenceLemmas
public import TauCeti.Algebra.Homology.Homotopy

/-!
# Bounded-below right derived functors from adapted resolutions

Let `F : C ⥤ D` be an additive functor between abelian categories, where `C` has enough
injectives, and let `F.rightDerivedFunctorPlus : DerivedCategory.Plus C ⥤ DerivedCategory.Plus D`
be Mathlib's bounded-below right derived functor. This file develops the adapted-resolution and
structural API for `F.rightDerivedFunctorPlus`:

* **Adapted resolutions:** for a class `P : ObjectProperty C` closed under isomorphisms, containing
  injectives, closed under cokernels of monomorphisms, and on whose short exact sequences `F` is
  exact, the derived unit `F.rightDerivedFunctorPlusUnit.app K` is an isomorphism for every
  `K : CochainComplex.Plus C` with terms in `P`
  (`CategoryTheory.Functor.isIso_rightDerivedFunctorPlusUnit_app_of_adapted`). Hence any
  quasi-isomorphism `ι : K ⟶ L` into a bounded-below `P`-complex computes
  `F.rightDerivedFunctorPlus.obj (Q.obj K) ≅ Q.obj (F(L))`
  (`CategoryTheory.Functor.rightDerivedFunctorPlusObjIsoOfResolution`), compatible with comparison
  maps to injective resolutions and natural in maps of complexes.
* **Homotopy, quasi-isomorphisms, shifts, cones, and truncations:** homotopic maps induce equal
  morphisms after `F.rightDerivedFunctorPlus`, quasi-isomorphisms induce isomorphisms, shifts
  commute with derived cohomology, mapping cone triangles induce distinguished triangles in
  `DerivedCategory.Plus`, and canonical truncations within the bounded-below range induce
  distinguished triangles preserved by `F.rightDerivedFunctorPlus`.

Exact-functor comparison and degree-zero recovery of classical right derived functors `RⁿF` are
proved in `TauCeti/Algebra/Homology/DerivedCategory/Plus/Comparison.lean`.

## References

* The Stacks Project, Derived Categories, §13.15–§13.16 (tags 05T8, 015E).
* M. Kashiwara, P. Schapira, *Categories and Sheaves*, Grundlehren 332, Springer, 2006, §13.3.
-/

public section

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor CategoryTheory.Triangulated
open CategoryTheory.Pretriangulated HomologicalComplex ZeroObject

universe w₁ w₂ v₁ v₂ u₁ u₂

namespace CategoryTheory.Functor

/-! ### Adapted resolutions for `rightDerivedFunctorPlus` -/

section Adapted

variable {C : Type u₁} [Category.{v₁} C] [Abelian C]
  {D : Type u₂} [Category.{v₂} D] [Abelian D]

section EmbeddingInt

variable [EnoughInjectives C] (K : CochainComplex C ℤ) (b : ℤ) [K.IsStrictlyGE b]

/-- Injective envelope of `K.X n` for `n ≥ b`, and `0` for `n < b`. -/
private def embeddingTermInt (n : ℤ) : C :=
  if n < b then 0 else Injective.under (K.X n)

private instance (n : ℤ) : Injective (embeddingTermInt K b n) := by
  dsimp [embeddingTermInt]
  split_ifs <;> infer_instance

/-- The bounded-below contractible injective complex `T` with `Tⁿ = Eⁿ⁺¹ ⊞ Eⁿ` and
differential `(a, b) ↦ (0, a)`. -/
private def embeddingComplexInt : CochainComplex C ℤ where
  X n := embeddingTermInt K b (n + 1) ⊞ embeddingTermInt K b n
  d i j :=
    if h : i + 1 = j then
      biprod.fst ≫ biprod.inr ≫ eqToHom (by subst h; rfl)
    else 0
  shape i j hij := dite_eq_right hij
  d_comp_d' i j k hij hjk := by
    obtain rfl : i + 1 = j := hij
    obtain rfl : i + 1 + 1 = k := hjk
    simp

private instance (n : ℤ) : Injective ((embeddingComplexInt K b).X n) := by
  dsimp [embeddingComplexInt]
  infer_instance

private instance : (embeddingComplexInt K b).IsStrictlyGE (b - 1) := by
  rw [CochainComplex.isStrictlyGE_iff]
  intro i hi
  have h1 : i + 1 < b := by omega
  have h2 : i < b := by omega
  change IsZero (embeddingTermInt K b (i + 1) ⊞ embeddingTermInt K b i)
  have hz1 : IsZero (embeddingTermInt K b (i + 1)) := by
    simp [embeddingTermInt, h1, isZero_zero]
  have hz2 : IsZero (embeddingTermInt K b i) := by
    simp [embeddingTermInt, h2, isZero_zero]
  rw [IsZero.iff_id_eq_zero]
  apply biprod.hom_ext
  · exact hz1.eq_of_tgt _ _
  · exact hz2.eq_of_tgt _ _

omit [K.IsStrictlyGE b] in
private lemma embeddingComplexInt_d (n : ℤ) :
    (embeddingComplexInt K b).d n (n + 1) = biprod.fst ≫ biprod.inr := by
  simp [embeddingComplexInt]

/-- Components of the contracting homotopy `(a, b) ↦ (b, 0)` of `embeddingComplexInt K b`. -/
private def embeddingComplexIntHom (i j : ℤ) :
    (embeddingComplexInt K b).X i ⟶ (embeddingComplexInt K b).X j :=
  if h : j + 1 = i then
    biprod.snd ≫ eqToHom (by subst h; rfl) ≫ biprod.inl
  else 0

omit [K.IsStrictlyGE b] in
private lemma embeddingComplexIntHom_succ (m : ℤ) :
    embeddingComplexIntHom K b (m + 1) m = biprod.snd ≫ biprod.inl := by
  dsimp only [embeddingComplexIntHom, embeddingComplexInt]
  simp only [↓reduceDIte, eqToHom_refl, Category.id_comp]

/-- Contracting homotopy `(a, b) ↦ (b, 0)` of `embeddingComplexInt K b`. -/
private def embeddingComplexIntHomotopy :
    Homotopy (𝟙 (embeddingComplexInt K b)) 0 where
  hom := embeddingComplexIntHom K b
  zero i j hij := dite_eq_right hij
  comm n := by
    obtain ⟨m, rfl⟩ : ∃ m : ℤ, n = m + 1 := ⟨n - 1, by omega⟩
    rw [dNext_eq _ (ComplexShape.up_mk (m + 1) (m + 1 + 1) rfl),
      prevD_eq _ (ComplexShape.up_mk m (m + 1) rfl),
      HomologicalComplex.id_f, HomologicalComplex.zero_f, add_zero]
    exact Eq.trans biprod.total.symm (congrArg₂ (· + ·)
      (by
        rw [embeddingComplexInt_d, embeddingComplexIntHom_succ]
        change biprod.fst ≫ biprod.inl = (biprod.fst ≫ biprod.inr) ≫ biprod.snd ≫ biprod.inl
        simp)
      (by
        rw [embeddingComplexInt_d, embeddingComplexIntHom_succ]
        change biprod.snd ≫ biprod.inr = (biprod.snd ≫ biprod.inl) ≫ biprod.fst ≫ biprod.inr
        simp))

/-- The degreewise monomorphism `K.X n ⟶ embeddingTermInt K b n`. -/
private def toEmbeddingTermInt (n : ℤ) : K.X n ⟶ embeddingTermInt K b n :=
  if h : n < b then 0
  else Injective.ι (K.X n) ≫ eqToHom (by simp [embeddingTermInt, h])

private instance (n : ℤ) : Mono (toEmbeddingTermInt K b n) := by
  dsimp [toEmbeddingTermInt]
  split_ifs with h
  · have hz : IsZero (K.X n) := K.isZero_of_isStrictlyGE b n h
    exact Preadditive.mono_of_cancel_zero _ fun _ _ ↦ hz.eq_of_tgt _ _
  · infer_instance

/-- The degreewise monomorphism `k ↦ (dk, k)` from `K` to `embeddingComplexInt K b`. -/
private def toEmbeddingComplexInt : K ⟶ embeddingComplexInt K b where
  f n := biprod.lift (K.d n (n + 1) ≫ toEmbeddingTermInt K b (n + 1)) (toEmbeddingTermInt K b n)
  comm' i j hij := by
    obtain rfl : i + 1 = j := hij
    rw [embeddingComplexInt_d]
    dsimp [embeddingComplexInt]
    apply biprod.hom_ext
    · simp [K.d_comp_d_assoc]
    · simp

private instance (n : ℤ) : Mono ((toEmbeddingComplexInt K b).f n) := by
  have : Mono ((toEmbeddingComplexInt K b).f n ≫ biprod.snd) := by
    rw [show (toEmbeddingComplexInt K b).f n ≫ biprod.snd = toEmbeddingTermInt K b n by
      dsimp [toEmbeddingComplexInt]
      exact biprod.lift_snd _ _]
    infer_instance
  exact mono_of_mono _ biprod.snd

omit [K.IsStrictlyGE b] in
private lemma acyclic_map_embeddingComplexInt (F : C ⥤ D) [F.Additive] :
    ((F.mapHomologicalComplex _).obj (embeddingComplexInt K b)).Acyclic :=
  Homotopy.acyclic ((Homotopy.ofEq ((F.mapHomologicalComplex _).map_id _).symm).trans
    ((F.mapHomotopy (embeddingComplexIntHomotopy K b)).trans
      (Homotopy.ofEq ((F.mapHomologicalComplex _).map_zero _ _))))

end EmbeddingInt

variable [EnoughInjectives C] (F : C ⥤ D) [F.Additive]
  (P : ObjectProperty C) [P.IsClosedUnderIsomorphisms]
  (hinj : ∀ (Y : C), Injective Y → P Y)
  (hP : ∀ S : ShortComplex C, S.ShortExact → P S.X₁ → P S.X₂ → P S.X₃)
  (hF : ∀ S : ShortComplex C, S.ShortExact → P S.X₁ → P S.X₂ → (S.map F).ShortExact)

include hinj hP hF in
/-- **Adapted bounded-below complexes preserve quasi-isomorphisms into injective complexes.**
For a quasi-isomorphism `i : K ⟶ ι(I)` from a bounded-below `P`-complex `K` to a bounded-below
complex `I` of injective objects, `F(i)` is a quasi-isomorphism. -/
theorem quasiIso_map_of_adapted_injective
    {K : CochainComplex.Plus C} (hK : ∀ n, P (K.obj.X n))
    {I : CochainComplex.Plus (InjectiveObject C)}
    (i : K ⟶ (InjectiveObject.ι C).mapCochainComplexPlus.obj I) [QuasiIso i.hom] :
    QuasiIso ((F.mapHomologicalComplex _).map i.hom) := by
  obtain ⟨b₁, hb₁⟩ := K.property
  obtain ⟨b₂, hb₂⟩ := I.property
  let b := min b₁ b₂
  have : K.obj.IsStrictlyGE b := K.obj.isStrictlyGE_of_ge b b₁ (min_le_left _ _)
  have hIge : ((InjectiveObject.ι C).mapCochainComplexPlus.obj I).obj.IsStrictlyGE b := by
    have : I.obj.IsStrictlyGE b := I.obj.isStrictlyGE_of_ge b b₂ (min_le_right _ _)
    exact inferInstanceAs
      (CochainComplex.IsStrictlyGE (((InjectiveObject.ι C).mapHomologicalComplex _).obj I.obj) b)
  let L := ((InjectiveObject.ι C).mapCochainComplexPlus.obj I).obj
  let T := embeddingComplexInt K.obj b
  let ψ : K.obj ⟶ T ⊞ L := biprod.lift (toEmbeddingComplexInt K.obj b) i.hom
  have hψ : ψ ≫ biprod.snd = i.hom := biprod.lift_snd _ _
  have : Mono ψ := HomologicalComplex.mono_of_mono_f _ fun n ↦ by
    have : Mono (ψ.f n ≫ (biprod.fst : T ⊞ L ⟶ T).f n) := by
      rw [← HomologicalComplex.comp_f, biprod.lift_fst]
      infer_instance
    exact mono_of_mono _ ((biprod.fst : T ⊞ L ⟶ T).f n)
  have hsplit := ShortComplex.Splitting.ofHasBinaryBiproduct T L
  have : QuasiIso (biprod.snd : T ⊞ L ⟶ L) :=
    hsplit.shortExact.quasiIso_g_iff.2 (Homotopy.acyclic (embeddingComplexIntHomotopy K.obj b))
  have : QuasiIso ψ := by
    have : QuasiIso (ψ ≫ biprod.snd) := by rw [hψ]; infer_instance
    exact quasiIso_of_comp_right ψ biprod.snd
  -- Form the cokernel sequence `0 ⟶ K ⟶ T ⊞ L ⟶ Q ⟶ 0`.
  let S := ShortComplex.mk ψ (cokernel.π ψ) (cokernel.condition ψ)
  have hS : S.ShortExact := ShortComplex.ShortExact.mk'
    (ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel ψ)) inferInstance inferInstance
  have hSn := (HomologicalComplex.shortExact_iff_degreewise_shortExact S).1 hS
  have hX₂ (n : ℤ) : P (S.X₂.X n) := by
    have : Injective (L.X n) := (I.obj.X n).property
    have : Injective (T.X n ⊞ L.X n) := inferInstance
    exact hinj _ (Injective.of_iso (HomologicalComplex.biprodXIso T L n).symm inferInstance)
  have hQge : S.X₃.IsStrictlyGE (b - 1) := by
    rw [CochainComplex.isStrictlyGE_iff]
    intro n hn
    have hTn : IsZero (T.X n) := T.isZero_of_isStrictlyGE (b - 1) n hn
    have hLn : IsZero (L.X n) := L.isZero_of_isStrictlyGE b n (by omega)
    have hTLn : IsZero (S.X₂.X n) := by
      refine IsZero.of_iso ?_ (HomologicalComplex.biprodXIso T L n)
      rw [IsZero.iff_id_eq_zero]
      exact biprod.hom_ext _ _ (hTn.eq_of_tgt _ _) (hLn.eq_of_tgt _ _)
    have := (hSn n).epi_g
    exact IsZero.of_epi ((cokernel.π ψ).f n) hTLn
  have hFS : (S.map (F.mapHomologicalComplex _)).ShortExact :=
    HomologicalComplex.shortExact_of_degreewise_shortExact _ fun n ↦
      hF _ (hSn n) (hK n) (hX₂ n)
  have : QuasiIso ((F.mapHomologicalComplex _).map ψ) :=
    hFS.quasiIso_f_iff.2 (HomologicalComplex.Acyclic.map_of_shortExact_of_isStrictlyGE F P hP hF
      (b - 1) (hS.quasiIso_f_iff.1 inferInstance) fun n ↦ hP _ (hSn n) (hK n) (hX₂ n))
  have : QuasiIso ((F.mapHomologicalComplex _).map (biprod.snd : T ⊞ L ⟶ L)) :=
    (hsplit.map (F.mapHomologicalComplex _)).shortExact.quasiIso_g_iff.2
      (acyclic_map_embeddingComplexInt K.obj b F)
  rw [← hψ, Functor.map_comp]
  infer_instance

variable [HasDerivedCategory.{w₁} C] [HasDerivedCategory.{w₂} D]

include hinj hP hF in
/-- **The derived unit is an isomorphism on bounded-below complexes in an adapted class.** -/
theorem isIso_rightDerivedFunctorPlusUnit_app_of_adapted
    (K : CochainComplex.Plus C) (hK : ∀ n, P (K.obj.X n)) :
    IsIso (F.rightDerivedFunctorPlusUnit.app K) := by
  obtain ⟨b, hb⟩ := K.property
  obtain ⟨I, _, i, hi⟩ := CochainComplex.Plus.exists_quasiIso_injective K b
  have : QuasiIso i.hom := hi
  have : QuasiIso (F.mapCochainComplexPlus.map i).hom :=
    F.quasiIso_map_of_adapted_injective P hinj hP hF hK i
  have hnat := F.rightDerivedFunctorPlusUnit.naturality i
  dsimp at hnat
  have : IsIso (DerivedCategory.Plus.Q.map i) := DerivedCategory.Plus.isIso_Q_map_of_quasiIso i
  have : IsIso (DerivedCategory.Plus.Q.map (F.mapCochainComplexPlus.map i)) :=
    DerivedCategory.Plus.isIso_Q_map_of_quasiIso (F.mapCochainComplexPlus.map i)
  have : IsIso (F.rightDerivedFunctorPlusUnit.app K ≫
      F.rightDerivedFunctorPlus.map (DerivedCategory.Plus.Q.map i)) := by
    rw [← hnat]
    infer_instance
  exact IsIso.of_isIso_comp_right _ (F.rightDerivedFunctorPlus.map (DerivedCategory.Plus.Q.map i))

include hinj hP hF in
/-- A quasi-isomorphism between bounded-below complexes in an adapted class remains a
quasi-isomorphism after applying `F`. -/
theorem quasiIso_map_of_adapted
    {K L : CochainComplex.Plus C} (f : K ⟶ L) [QuasiIso f.hom]
    (hK : ∀ n, P (K.obj.X n)) (hL : ∀ n, P (L.obj.X n)) :
    QuasiIso ((F.mapHomologicalComplex _).map f.hom) := by
  have := F.isIso_rightDerivedFunctorPlusUnit_app_of_adapted P hinj hP hF K hK
  have := F.isIso_rightDerivedFunctorPlusUnit_app_of_adapted P hinj hP hF L hL
  have : IsIso (DerivedCategory.Plus.Q.map f) := DerivedCategory.Plus.isIso_Q_map_of_quasiIso f
  have hnat := F.rightDerivedFunctorPlusUnit.naturality f
  dsimp at hnat
  have hQ : IsIso (DerivedCategory.Plus.Q.map (F.mapCochainComplexPlus.map f)) := by
    have : IsIso (DerivedCategory.Plus.Q.map (F.mapCochainComplexPlus.map f) ≫
        F.rightDerivedFunctorPlusUnit.app L) := by
      rw [hnat]
      infer_instance
    exact IsIso.of_isIso_comp_right _ (F.rightDerivedFunctorPlusUnit.app L)
  rw [quasiIso_iff]
  intro n
  rw [quasiIsoAt_iff_isIso_homologyMap]
  have hnatH := (DerivedCategory.Plus.homologyFunctorFactors D n).hom.naturality
    (F.mapCochainComplexPlus.map f)
  have hcomp : IsIso ((DerivedCategory.Plus.homologyFunctorFactors D n).hom.app
      (F.mapCochainComplexPlus.obj K) ≫
      HomologicalComplex.homologyMap ((F.mapHomologicalComplex (.up ℤ)).map f.hom) n) := by
    change IsIso ((DerivedCategory.Plus.homologyFunctorFactors D n).hom.app
      (F.mapCochainComplexPlus.obj K) ≫
      (CochainComplex.Plus.ι D ⋙ HomologicalComplex.homologyFunctor D (.up ℤ) n).map
        (F.mapCochainComplexPlus.map f))
    rw [← hnatH]
    exact inferInstanceAs (IsIso ((DerivedCategory.Plus.homologyFunctor D n).map
      (DerivedCategory.Plus.Q.map (F.mapCochainComplexPlus.map f)) ≫
      (DerivedCategory.Plus.homologyFunctorFactors D n).hom.app (F.mapCochainComplexPlus.obj L)))
  exact IsIso.of_isIso_comp_left
    ((DerivedCategory.Plus.homologyFunctorFactors D n).hom.app (F.mapCochainComplexPlus.obj K)) _

include hinj hP hF in
/-- **Bounded-below right derived functors from adapted resolutions.** Given a quasi-isomorphism
`ι : K ⟶ L` in `CochainComplex.Plus C` with terms of `L` in an `F`-adapted class `P`,
`RF⁺(Q(K)) ≅ Q(F(L))`. -/
def rightDerivedFunctorPlusObjIsoOfResolution
    {K L : CochainComplex.Plus C} (ι : K ⟶ L) [QuasiIso ι.hom] (hL : ∀ n, P (L.obj.X n)) :
    F.rightDerivedFunctorPlus.obj (DerivedCategory.Plus.Q.obj K) ≅
      DerivedCategory.Plus.Q.obj (F.mapCochainComplexPlus.obj L) :=
  have := DerivedCategory.Plus.isIso_Q_map_of_quasiIso ι
  have := F.isIso_rightDerivedFunctorPlusUnit_app_of_adapted P hinj hP hF L hL
  F.rightDerivedFunctorPlus.mapIso (asIso (DerivedCategory.Plus.Q.map ι)) ≪≫
    (asIso (F.rightDerivedFunctorPlusUnit.app L)).symm

include hinj hP hF in
/-- Compatibility of `rightDerivedFunctorPlusObjIsoOfResolution` with any comparison map
`φ : L ⟶ M` to an adapted (in particular injective) resolution `κ : K ⟶ M`. -/
@[reassoc]
lemma rightDerivedFunctorPlusObjIsoOfResolution_hom_comp
    {K L M : CochainComplex.Plus C} (ι : K ⟶ L) [QuasiIso ι.hom] (hL : ∀ n, P (L.obj.X n))
    (φ : L ⟶ M) :
    (F.rightDerivedFunctorPlusObjIsoOfResolution P hinj hP hF ι hL).hom ≫
        DerivedCategory.Plus.Q.map (F.mapCochainComplexPlus.map φ) ≫
        F.rightDerivedFunctorPlusUnit.app M =
      F.rightDerivedFunctorPlus.map (DerivedCategory.Plus.Q.map (ι ≫ φ)) := by
  have := DerivedCategory.Plus.isIso_Q_map_of_quasiIso ι
  have := F.isIso_rightDerivedFunctorPlusUnit_app_of_adapted P hinj hP hF L hL
  dsimp [rightDerivedFunctorPlusObjIsoOfResolution]
  have hnat := F.rightDerivedFunctorPlusUnit.naturality φ
  dsimp at hnat
  rw [hnat, Category.assoc, IsIso.inv_hom_id_assoc, ← Functor.map_comp, ← Functor.map_comp]

include hinj hP hF in
/-- Naturality of `rightDerivedFunctorPlusObjIsoOfResolution` in morphisms of resolved complexes. -/
@[reassoc]
lemma rightDerivedFunctorPlusObjIsoOfResolution_hom_naturality
    {K K' L L' : CochainComplex.Plus C}
    (ι : K ⟶ L) [QuasiIso ι.hom] (hL : ∀ n, P (L.obj.X n))
    (κ : K' ⟶ L') [QuasiIso κ.hom] (hL' : ∀ n, P (L'.obj.X n))
    (f : K ⟶ K') (φ : L ⟶ L') (hφ : ι ≫ φ = f ≫ κ) :
    F.rightDerivedFunctorPlus.map (DerivedCategory.Plus.Q.map f) ≫
        (F.rightDerivedFunctorPlusObjIsoOfResolution P hinj hP hF κ hL').hom =
      (F.rightDerivedFunctorPlusObjIsoOfResolution P hinj hP hF ι hL).hom ≫
        DerivedCategory.Plus.Q.map (F.mapCochainComplexPlus.map φ) := by
  have := F.isIso_rightDerivedFunctorPlusUnit_app_of_adapted P hinj hP hF L' hL'
  rw [← cancel_mono (F.rightDerivedFunctorPlusUnit.app L'), Category.assoc, Category.assoc,
    F.rightDerivedFunctorPlusObjIsoOfResolution_hom_comp P hinj hP hF ι hL φ, hφ,
    Functor.map_comp, Functor.map_comp]
  dsimp [rightDerivedFunctorPlusObjIsoOfResolution]
  rw [Category.assoc, IsIso.inv_hom_id, Category.comp_id]

include hinj hP hF in
/-- Cohomology of `RF⁺(Q(K))` computed by an adapted resolution `ι : K ⟶ L`. -/
def rightDerivedFunctorPlusHomologyObjIsoOfResolution
    {K L : CochainComplex.Plus C} (ι : K ⟶ L) [QuasiIso ι.hom] (hL : ∀ n, P (L.obj.X n))
    (m : ℤ) :
    (DerivedCategory.Plus.homologyFunctor D m).obj
        (F.rightDerivedFunctorPlus.obj (DerivedCategory.Plus.Q.obj K)) ≅
      ((F.mapHomologicalComplex _).obj L.obj).homology m :=
  (DerivedCategory.Plus.homologyFunctor D m).mapIso
      (F.rightDerivedFunctorPlusObjIsoOfResolution P hinj hP hF ι hL) ≪≫
    (DerivedCategory.Plus.homologyFunctorFactors D m).app (F.mapCochainComplexPlus.obj L)

include hinj hP hF in
/-- A functorial adapted resolution `ι : 𝟭 _ ⟶ R` on `CochainComplex.Plus C` computes
`Q ⋙ F.rightDerivedFunctorPlus` naturally. -/
def rightDerivedFunctorPlusIsoOfResolution
    (R : CochainComplex.Plus C ⥤ CochainComplex.Plus C)
    (ι : 𝟭 (CochainComplex.Plus C) ⟶ R) [∀ K, QuasiIso (ι.app K).hom]
    (hR : ∀ K n, P ((R.obj K).obj.X n)) :
    DerivedCategory.Plus.Q ⋙ F.rightDerivedFunctorPlus ≅
      R ⋙ F.mapCochainComplexPlus ⋙ DerivedCategory.Plus.Q :=
  NatIso.ofComponents
    (fun K ↦ F.rightDerivedFunctorPlusObjIsoOfResolution P hinj hP hF (ι.app K) (hR K))
    (fun f ↦ F.rightDerivedFunctorPlusObjIsoOfResolution_hom_naturality P hinj hP hF
      (ι.app _) (hR _) (ι.app _) (hR _) f (R.map f) (ι.naturality f).symm)

include hinj hP hF in
/-- Each component of `rightDerivedFunctorPlusIsoOfResolution` is the objectwise resolution
isomorphism. -/
@[simp]
lemma rightDerivedFunctorPlusIsoOfResolution_app
    (R : CochainComplex.Plus C ⥤ CochainComplex.Plus C)
    (ι : 𝟭 (CochainComplex.Plus C) ⟶ R) [∀ K, QuasiIso (ι.app K).hom]
    (hR : ∀ K n, P ((R.obj K).obj.X n)) (K : CochainComplex.Plus C) :
    (F.rightDerivedFunctorPlusIsoOfResolution P hinj hP hF R ι hR).app K =
      F.rightDerivedFunctorPlusObjIsoOfResolution P hinj hP hF (ι.app K) (hR K) := by
  simp [rightDerivedFunctorPlusIsoOfResolution]

end Adapted


/-! ### Homotopy, quasi-isomorphism, shift, cone, and truncation compatibilities -/

section Structural

variable {C : Type u₁} [Category.{v₁} C] [Abelian C] [HasDerivedCategory.{w₁} C]
  [EnoughInjectives C]
  {D : Type u₂} [Category.{v₂} D] [Abelian D] [HasDerivedCategory.{w₂} D]
  (F : C ⥤ D) [F.Additive]

/-- Homotopic maps of bounded-below cochain complexes induce the same morphism after
`F.rightDerivedFunctorPlus`. -/
lemma rightDerivedFunctorPlus_map_Q_eq_of_homotopy {K L : CochainComplex.Plus C} {f g : K ⟶ L}
    (h : Homotopy f.hom g.hom) :
    F.rightDerivedFunctorPlus.map (DerivedCategory.Plus.Q.map f) =
      F.rightDerivedFunctorPlus.map (DerivedCategory.Plus.Q.map g) := by
  rw [DerivedCategory.Plus.Q_map_eq_of_homotopy h]

/-- A quasi-isomorphism of bounded-below cochain complexes induces an isomorphism after
`F.rightDerivedFunctorPlus`. -/
instance isIso_rightDerivedFunctorPlus_map_Q_of_quasiIso {K L : CochainComplex.Plus C}
    (f : K ⟶ L) [QuasiIso f.hom] :
    IsIso (F.rightDerivedFunctorPlus.map (DerivedCategory.Plus.Q.map f)) :=
  have := DerivedCategory.Plus.isIso_Q_map_of_quasiIso f
  inferInstance

/-- Shift compatibility for bounded-below right derived cohomology:
`Hᵐ(RF⁺(X⟦a⟧)) ≅ Hᵐ⁺ᵃ(RF⁺(X))`, naturally in `X`. -/
def rightDerivedFunctorPlusShiftCompHomologyIso (a m : ℤ) :
    shiftFunctor (DerivedCategory.Plus C) a ⋙ F.rightDerivedFunctorPlus ⋙
        DerivedCategory.Plus.homologyFunctor D m ≅
      F.rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.homologyFunctor D (m + a) :=
  (Functor.associator _ _ _).symm ≪≫
    isoWhiskerRight (F.rightDerivedFunctorPlus.commShiftIso a)
      (DerivedCategory.Plus.homologyFunctor D m) ≪≫
    Functor.associator _ _ _ ≪≫
    isoWhiskerLeft F.rightDerivedFunctorPlus
      ((DerivedCategory.Plus.homologyFunctor D 0).shiftIso a m (m + a) (add_comm a m))

/-- The mapping cone of a morphism `f : K ⟶ L` in `CochainComplex.Plus C`, as a bounded-below
cochain complex. -/
def _root_.CochainComplex.Plus.mappingCone {K L : CochainComplex.Plus C} (f : K ⟶ L) :
    CochainComplex.Plus C :=
  ⟨CochainComplex.mappingCone f.hom, by
    obtain ⟨n₁, _⟩ := K.property
    obtain ⟨n₂, _⟩ := L.property
    exact ⟨min (n₁ - 1) n₂, CochainComplex.isStrictlyGE_mappingCone f.hom n₁ n₂
      (min (n₁ - 1) n₂) (by omega) (by omega)⟩⟩

/-- The connecting morphism `cone(f) ⟶ K⟦1⟧` of a mapping cone triangle in
`CochainComplex.Plus C`. -/
private def mappingConeMor₃ {K L : CochainComplex.Plus C} (f : K ⟶ L) :
    CochainComplex.Plus.mappingCone f ⟶ K⟦(1 : ℤ)⟧ :=
  (CochainComplex.Plus.fullyFaithfulι C).preimage
    ((CochainComplex.mappingCone.triangle f.hom).mor₃ ≫
      ((CochainComplex.Plus.ι C).commShiftIso (1 : ℤ)).inv.app K)

/-- The mapping cone triangle `K ⟶ L ⟶ cone(f) ⟶ K⟦1⟧` in `CochainComplex.Plus C`. -/
def _root_.CochainComplex.Plus.mappingConeTriangle {K L : CochainComplex.Plus C} (f : K ⟶ L) :
    Triangle (CochainComplex.Plus C) :=
  Triangle.mk f
    (ObjectProperty.homMk (CochainComplex.mappingCone.inr f.hom) :
      L ⟶ CochainComplex.Plus.mappingCone f)
    (mappingConeMor₃ f)

omit [EnoughInjectives C] in
/-- The image of a mapping cone triangle in `CochainComplex.Plus C` under `DerivedCategory.Plus.Q`
is distinguished. -/
lemma _root_.DerivedCategory.Plus.mappingConeTriangle_distinguished
    {K L : CochainComplex.Plus C} (f : K ⟶ L) :
    DerivedCategory.Plus.Q.mapTriangle.obj (CochainComplex.Plus.mappingConeTriangle f) ∈
      distTriang (DerivedCategory.Plus C) := by
  rw [← DerivedCategory.Plus.ι.map_distinguished_iff]
  refine isomorphic_distinguished _ (DerivedCategory.mappingCone_triangle_distinguished f.hom) _ ?_
  refine Triangle.isoMk _ _
    ((DerivedCategory.Plus.QCompιIso C).app K)
    ((DerivedCategory.Plus.QCompιIso C).app L)
    ((DerivedCategory.Plus.QCompιIso C).app (CochainComplex.Plus.mappingCone f)) ?_ ?_ ?_
  · exact (DerivedCategory.Plus.QCompιIso C).hom.naturality f
  · exact (DerivedCategory.Plus.QCompιIso C).hom.naturality
      (ObjectProperty.homMk (CochainComplex.mappingCone.inr f.hom) :
        L ⟶ CochainComplex.Plus.mappingCone f)
  · have hnat := (DerivedCategory.Plus.QCompιIso C).hom.naturality (mappingConeMor₃ f)
    have hsh := NatTrans.congr_app
      (NatTrans.CommShift.shift_comm (τ := (DerivedCategory.Plus.QCompιIso C).hom) (1 : ℤ)) K
    have hmor : (CochainComplex.Plus.ι C).map (mappingConeMor₃ f) ≫
        ((CochainComplex.Plus.ι C).commShiftIso (1 : ℤ)).hom.app K =
      (CochainComplex.mappingCone.triangle f.hom).mor₃ := by
      have hpre : (CochainComplex.Plus.ι C).map (mappingConeMor₃ f) =
          (CochainComplex.mappingCone.triangle f.hom).mor₃ ≫
            ((CochainComplex.Plus.ι C).commShiftIso (1 : ℤ)).inv.app K :=
        (CochainComplex.Plus.fullyFaithfulι C).map_preimage _
      exact (congrArg
          (· ≫ ((CochainComplex.Plus.ι C).commShiftIso (1 : ℤ)).hom.app K) hpre).trans
        ((Category.assoc _ _ _).trans (by rw [Iso.inv_hom_id_app]; exact Category.comp_id _))
    change (DerivedCategory.Plus.ι.map (DerivedCategory.Plus.Q.map (mappingConeMor₃ f) ≫
            (DerivedCategory.Plus.Q.commShiftIso (1 : ℤ)).hom.app K) ≫
          (DerivedCategory.Plus.ι.commShiftIso (1 : ℤ)).hom.app
            (DerivedCategory.Plus.Q.obj K)) ≫
        ((DerivedCategory.Plus.QCompιIso C).hom.app K)⟦(1 : ℤ)⟧' =
      (DerivedCategory.Plus.QCompιIso C).hom.app (CochainComplex.Plus.mappingCone f) ≫
        (DerivedCategory.Q.map (CochainComplex.mappingCone.triangle f.hom).mor₃ ≫
          (DerivedCategory.Q.commShiftIso (1 : ℤ)).hom.app ((CochainComplex.Plus.ι C).obj K))
    simp only [Functor.map_comp, Category.assoc]
    dsimp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
      Functor.comp_map] at hnat hsh
    simp only [Functor.commShiftIso_comp_hom_app, Category.assoc] at hsh
    rw [hsh, reassoc_of% hnat, ← Functor.map_comp_assoc, hmor]

/-- `F.rightDerivedFunctorPlus` sends the mapping cone triangle of `f : K ⟶ L` to a distinguished
triangle in `DerivedCategory.Plus D`. -/
lemma rightDerivedFunctorPlus_mappingConeTriangle_distinguished
    {K L : CochainComplex.Plus C} (f : K ⟶ L) :
    F.rightDerivedFunctorPlus.mapTriangle.obj
        (DerivedCategory.Plus.Q.mapTriangle.obj (CochainComplex.Plus.mappingConeTriangle f)) ∈
      distTriang (DerivedCategory.Plus D) :=
  F.rightDerivedFunctorPlus.map_distinguished _
    (DerivedCategory.Plus.mappingConeTriangle_distinguished f)

/-- The canonical `≤ n` truncation of a bounded-below cochain complex stays bounded below. -/
def _root_.CochainComplex.Plus.truncLE (K : CochainComplex.Plus C) (n : ℤ) :
    CochainComplex.Plus C :=
  ⟨K.obj.truncLE n, by
    obtain ⟨b, _⟩ := K.property
    exact ⟨b, inferInstance⟩⟩

/-- The canonical `≥ n` truncation of a bounded-below cochain complex stays bounded below. -/
def _root_.CochainComplex.Plus.truncGE (K : CochainComplex.Plus C) (n : ℤ) :
    CochainComplex.Plus C :=
  ⟨K.obj.truncGE n, by
    obtain ⟨b, _⟩ := K.property
    exact ⟨b, inferInstance⟩⟩

/-- The canonical morphism `τ_{≤ n} K ⟶ K` in `CochainComplex.Plus C`. -/
def _root_.CochainComplex.Plus.ιTruncLE (K : CochainComplex.Plus C) (n : ℤ) :
    K.truncLE n ⟶ K :=
  ObjectProperty.homMk (K.obj.ιTruncLE n)

/-- The canonical morphism `K ⟶ τ_{≥ n} K` in `CochainComplex.Plus C`. -/
def _root_.CochainComplex.Plus.πTruncGE (K : CochainComplex.Plus C) (n : ℤ) :
    K ⟶ K.truncGE n :=
  ObjectProperty.homMk (K.obj.πTruncGE n)

/-- `F.rightDerivedFunctorPlus` sends the canonical truncation triangle
`τ_{≤ n} X ⟶ X ⟶ τ_{≥ n+1} X ⟶ (τ_{≤ n} X)⟦1⟧` in `DerivedCategory.Plus C` to a
distinguished triangle in `DerivedCategory.Plus D`. -/
lemma rightDerivedFunctorPlus_truncTriangle_distinguished
    (X : DerivedCategory.Plus C) (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁ := by omega) :
    F.rightDerivedFunctorPlus.mapTriangle.obj
        ((DerivedCategory.Plus.TStructure.t.triangleLEGE n₀ n₁ h).obj X) ∈
      distTriang (DerivedCategory.Plus D) :=
  F.rightDerivedFunctorPlus.map_distinguished _
    (DerivedCategory.Plus.TStructure.t.triangleLEGE_distinguished n₀ n₁ h X)

/-- If `K : CochainComplex.Plus C` has cohomology concentrated in degrees `≥ n`, then
`K ⟶ τ_{≥ n} K` induces an isomorphism after `F.rightDerivedFunctorPlus`. -/
instance isIso_rightDerivedFunctorPlus_map_Q_πTruncGE
    (K : CochainComplex.Plus C) (n : ℤ) [K.obj.IsGE n] :
    IsIso (F.rightDerivedFunctorPlus.map (DerivedCategory.Plus.Q.map (K.πTruncGE n))) :=
  have : QuasiIso (K.πTruncGE n).hom := inferInstanceAs (QuasiIso (K.obj.πTruncGE n))
  F.isIso_rightDerivedFunctorPlus_map_Q_of_quasiIso (K.πTruncGE n)

/-- If `K : CochainComplex.Plus C` has cohomology concentrated in degrees `≤ n`, then
`τ_{≤ n} K ⟶ K` induces an isomorphism after `F.rightDerivedFunctorPlus`. -/
instance isIso_rightDerivedFunctorPlus_map_Q_ιTruncLE
    (K : CochainComplex.Plus C) (n : ℤ) [K.obj.IsLE n] :
    IsIso (F.rightDerivedFunctorPlus.map (DerivedCategory.Plus.Q.map (K.ιTruncLE n))) :=
  have : QuasiIso (K.ιTruncLE n).hom := inferInstanceAs (QuasiIso (K.obj.ιTruncLE n))
  F.isIso_rightDerivedFunctorPlus_map_Q_of_quasiIso (K.ιTruncLE n)

end Structural

end CategoryTheory.Functor
