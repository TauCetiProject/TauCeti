/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.HomologicalComplexBiprod
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.CategoryTheory.ObjectProperty.ClosedUnderIsomorphisms
public import TauCeti.Algebra.Homology.HomologicalComplex.Acyclic
public import TauCeti.Algebra.Homology.Homotopy
public import TauCeti.Algebra.Homology.HomologySequenceLemmas
public import TauCeti.CategoryTheory.Abelian.Injective.Resolution

/-!
# Right derived functors from acyclic resolutions

Let `F : C ⥤ D` be an additive functor between abelian categories, where `C` has enough
injectives. Mathlib defines the right derived functors `RⁿF` through injective resolutions. This
file shows that they may be computed from resolutions by objects of a class `P` adapted to `F`, in
the following sense:

* every injective object lies in `P`, and `P` is closed under isomorphisms;
* in a short exact sequence `0 ⟶ A ⟶ B ⟶ C ⟶ 0` with `A` and `B` in `P`, also `C` lies in `P`;
* `F` sends such a short exact sequence to a short exact sequence.

For instance, flasque sheaves form such a class for the global sections functor. If
`0 ⟶ X ⟶ K⁰ ⟶ K¹ ⟶ ⋯` is a resolution of `X` by objects of `P`, given as a quasi-isomorphism
`ι : X[0] ⟶ K`, then `F` applied to a comparison map `K ⟶ I` to an injective resolution of `X` is
a quasi-isomorphism (`CategoryTheory.InjectiveResolution.quasiIso_map_of_comp_eq`), so
`RⁿF(X) ≅ Hⁿ(F(K))` (`CategoryTheory.Functor.rightDerivedObjIsoOfResolution`).

The proof has three steps.

* `F` sends acyclic complexes `0 ⟶ Q⁰ ⟶ Q¹ ⟶ ⋯` with terms in `P` to acyclic complexes
  (`HomologicalComplex.Acyclic.map_of_shortExact`, in
  `TauCeti/Algebra/Homology/HomologicalComplex/Acyclic.lean`).
* A comparison map `φ : K ⟶ I` exists (`CategoryTheory.InjectiveResolution.descOfQuasiIso`, which
  only uses the exactness of `K` and the injectivity of the terms of `I`) and is unique up to
  homotopy (`CategoryTheory.InjectiveResolution.homotopyOfQuasiIso`); both are in
  `TauCeti/CategoryTheory/Abelian/Injective/Resolution.lean`.
* Adding to `I` a contractible complex `T` of injective objects with a morphism `χ : K ⟶ T` which
  is a monomorphism in positive degrees, the map `(χ, φ) : K ⟶ T ⊞ I` becomes a degreewise
  monomorphism and stays a quasi-isomorphism. Its cokernel `Q` is acyclic with terms in `P`, so
  `F` keeps the short exact sequence of complexes `0 ⟶ K ⟶ T ⊞ I ⟶ Q ⟶ 0` exact and sends `Q`
  to an acyclic complex. Hence `F(χ, φ)` is a quasi-isomorphism, and so is `F(φ)`, since `F(T)`
  is contractible.

## Main definitions and results

* `CategoryTheory.InjectiveResolution.quasiIso_map_of_comp_eq`: `F` applied to a comparison map
  from a `P`-resolution to an injective resolution is a quasi-isomorphism.
* `CategoryTheory.Functor.rightDerivedObjIsoOfResolution`: the isomorphism `RⁿF(X) ≅ Hⁿ(F(K))`
  for a `P`-resolution `K` of `X`, and
  `CategoryTheory.Functor.rightDerivedObjIsoOfResolution_hom_comp_homologyMap`, its
  characterization through any injective resolution.
* `CategoryTheory.Functor.rightDerivedObjIsoOfResolution_hom_naturality`: compatibility with
  morphisms of augmented resolutions.
* `CategoryTheory.Functor.rightDerivedIsoOfResolution`: the natural isomorphism for a
  functorial adapted resolution.

## References

* The Stacks Project, Derived Categories, Lemma 13.15.6 (tag 05T8) and Lemma 13.16.7
  (tag 015E).
* M. Kashiwara, P. Schapira, *Categories and Sheaves*, Grundlehren 332, Springer, 2006,
  Definition 13.3.4 and Corollary 13.3.8, where such classes are called `F`-injective.
-/

public section

noncomputable section

open CategoryTheory Limits HomologicalComplex

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.InjectiveResolution

open CochainComplex

variable {C : Type u₁} [Category.{v₁} C] [Abelian C] {D : Type u₂} [Category.{v₂} D] [Abelian D]

/-! ### A contractible complex of injective objects receiving a resolution

For a complex `K`, let `Eⁿ` be an injective object containing `Kⁿ` for `n ≥ 1`, and `E⁰ = 0`.
The complex `T` with `Tⁿ = Eⁿ⁺¹ ⊞ Eⁿ` and differential `(a, b) ↦ (0, a)` is contractible, and
`k ↦ (dk, k)` is a morphism `K ⟶ T` which is a monomorphism in every positive degree. -/

section Embedding

variable [EnoughInjectives C] (K : CochainComplex C ℕ)

open ZeroObject in
/-- The object `Eⁿ`: zero in degree `0`, and an injective object containing `Kⁿ` in degree
`n ≥ 1`. -/
private def embeddingTerm : ℕ → C
  | 0 => 0
  | n + 1 => Injective.under (K.X (n + 1))

private instance (n : ℕ) : Injective (embeddingTerm K n) := by
  cases n <;> dsimp [embeddingTerm] <;> infer_instance

/-- The contractible complex `T`, with `Tⁿ = Eⁿ⁺¹ ⊞ Eⁿ` and differential `(a, b) ↦ (0, a)`. It is
reducible so that its terms are seen as biproducts. -/
private abbrev embeddingComplex : CochainComplex C ℕ :=
  CochainComplex.of (fun n ↦ embeddingTerm K (n + 1) ⊞ embeddingTerm K n)
    (fun _ ↦ biprod.fst ≫ biprod.inr) (by simp)

private instance (n : ℕ) : Injective ((embeddingComplex K).X n) := by
  dsimp [embeddingComplex]
  infer_instance

private lemma embeddingComplex_d (n : ℕ) :
    (embeddingComplex K).d n (n + 1) = biprod.fst ≫ biprod.inr := by
  simp only [CochainComplex.of_d]

/-- The components `(a, b) ↦ (b, 0)` of the contracting homotopy of `embeddingComplex K`. -/
private def embeddingComplexHomotopyHom :
    ∀ i j, (ComplexShape.up ℕ).Rel j i → ((embeddingComplex K).X i ⟶ (embeddingComplex K).X j)
  | _, _, rfl => biprod.snd ≫ biprod.inl

private lemma embeddingComplexHomotopyHom_succ (n : ℕ) (h : (ComplexShape.up ℕ).Rel n (n + 1)) :
    embeddingComplexHomotopyHom K (n + 1) n h = biprod.snd ≫ biprod.inl :=
  rfl

/-- The complex `embeddingComplex K` is contractible. -/
private def embeddingComplexHomotopy : Homotopy (𝟙 (embeddingComplex K)) 0 :=
  (Homotopy.ofEq (by
    refine HomologicalComplex.hom_ext _ _ fun n ↦ ?_
    rcases n with _ | n
    · rw [Homotopy.nullHomotopicMap'_f_of_not_rel_right (ComplexShape.up_mk 0 1 rfl) (by simp),
        embeddingComplex_d]
      refine biprod.hom_ext _ _ ?_ ?_
      · simp [embeddingComplexHomotopyHom_succ]
      · exact (isZero_zero C).eq_of_tgt _ _
    · rw [Homotopy.nullHomotopicMap'_f (ComplexShape.up_mk n (n + 1) rfl)
        (ComplexShape.up_mk (n + 1) (n + 1 + 1) rfl), embeddingComplex_d, embeddingComplex_d]
      simp only [embeddingComplexHomotopyHom_succ, HomologicalComplex.id_f]
      refine biprod.hom_ext _ _ ?_ ?_
      · simp only [Category.id_comp, Preadditive.add_comp, Category.assoc, biprod.inl_fst,
          biprod.inr_fst, comp_zero, add_zero]
        rw [Category.comp_id, biprod.inr_snd, Category.comp_id]
      · simp)).trans
    (Homotopy.nullHomotopy' (embeddingComplexHomotopyHom K))

/-- The monomorphism `Kⁿ ⟶ Eⁿ` for `n ≥ 1`, which is zero for `n = 0`. -/
private def toEmbeddingTerm : ∀ n, K.X n ⟶ embeddingTerm K n
  | 0 => 0
  | n + 1 => Injective.ι (K.X (n + 1))

/-- The morphism `k ↦ (dk, k)` from `K` to `embeddingComplex K`. -/
private def toEmbeddingComplex : K ⟶ embeddingComplex K where
  f n := biprod.lift (K.d n (n + 1) ≫ toEmbeddingTerm K (n + 1)) (toEmbeddingTerm K n)
  comm' i j hij := by
    obtain rfl : i + 1 = j := hij
    rw [embeddingComplex_d]
    apply biprod.hom_ext <;>
      simp only [Category.assoc, biprod.lift_fst, biprod.lift_snd, biprod.inr_fst,
        biprod.inr_snd, comp_zero, Category.comp_id, K.d_comp_d_assoc, zero_comp]

private instance (n : ℕ) : Mono (toEmbeddingTerm K (n + 1)) :=
  Injective.ι_mono _

private lemma toEmbeddingComplex_f_snd (n : ℕ) :
    (toEmbeddingComplex K).f n ≫ biprod.snd = toEmbeddingTerm K n :=
  biprod.lift_snd _ _

private instance (n : ℕ) : Mono ((toEmbeddingComplex K).f (n + 1)) := by
  have : Mono ((toEmbeddingComplex K).f (n + 1) ≫ biprod.snd) := by
    rw [toEmbeddingComplex_f_snd]
    infer_instance
  exact mono_of_mono _ biprod.snd

private lemma toEmbeddingComplex_f_zero_fst :
    (toEmbeddingComplex K).f 0 ≫ biprod.fst = K.d 0 1 ≫ toEmbeddingTerm K 1 :=
  biprod.lift_fst _ _

/-- The complex `F(embeddingComplex K)` is acyclic, since `embeddingComplex K` is contractible. -/
private lemma acyclic_map_embeddingComplex (F : C ⥤ D) [F.Additive] :
    ((F.mapHomologicalComplex _).obj (embeddingComplex K)).Acyclic :=
  Homotopy.acyclic ((Homotopy.ofEq ((F.mapHomologicalComplex _).map_id _).symm).trans
    (((F.mapHomotopy (embeddingComplexHomotopy K))).trans
      (Homotopy.ofEq ((F.mapHomologicalComplex _).map_zero _ _))))

end Embedding

section Comparison

variable [EnoughInjectives C] (F : C ⥤ D) [F.Additive] (P : ObjectProperty C)
  [P.IsClosedUnderIsomorphisms] (hinj : ∀ (Y : C), Injective Y → P Y)
  (hP : ∀ S : ShortComplex C, S.ShortExact → P S.X₁ → P S.X₂ → P S.X₃)
  (hF : ∀ S : ShortComplex C, S.ShortExact → P S.X₁ → P S.X₂ → (S.map F).ShortExact)
  {X : C} {K : CochainComplex C ℕ} (ι : (single₀ C).obj X ⟶ K) [QuasiIso ι]
  (hK : ∀ n, P (K.X n))

/-- The morphism `(χ, φ) : K ⟶ T ⊞ I` is a monomorphism, where `χ : K ⟶ T` is
`toEmbeddingComplex K` and `φ : K ⟶ I` is compatible with `ι` and an injective resolution `I`. -/
private lemma mono_lift_toEmbeddingComplex {I : InjectiveResolution X} (φ : K ⟶ I.cocomplex)
    (hφ : ι ≫ φ = I.ι) : Mono (biprod.lift (toEmbeddingComplex K) φ) := by
  refine HomologicalComplex.mono_of_mono_f _ fun n ↦ ?_
  rcases n with _ | n
  · -- in degree `0`, the kernel of `K⁰ ⟶ T⁰` is `X`, on which `φ` is the monomorphism `X ⟶ I⁰`
    refine Preadditive.mono_of_cancel_zero _ fun {W} g hg ↦ ?_
    have h₁ : g ≫ (toEmbeddingComplex K).f 0 = 0 := by
      simpa using hg =≫ (biprod.fst : embeddingComplex K ⊞ I.cocomplex ⟶ _).f 0
    have h₂ : g ≫ φ.f 0 = 0 := by
      simpa using hg =≫ (biprod.snd : embeddingComplex K ⊞ I.cocomplex ⟶ _).f 0
    have h₃ : g ≫ K.d 0 1 = 0 := by
      rw [← cancel_mono (toEmbeddingTerm K 1), Category.assoc, ← toEmbeddingComplex_f_zero_fst,
        ← Category.assoc, h₁, zero_comp, zero_comp]
    have hS := exact_f_zero_of_quasiIsoAt ι
    rw [← hS.lift_f g h₃] at h₂ ⊢
    have : hS.lift g h₃ ≫ I.ι.f 0 = 0 := by
      rw [← h₂, Category.assoc, ← HomologicalComplex.comp_f, hφ]
    rw [(cancel_mono (I.ι.f 0)).1 (this.trans (zero_comp).symm), zero_comp]
  · have : Mono ((biprod.lift (toEmbeddingComplex K) φ).f (n + 1) ≫
        (biprod.fst : embeddingComplex K ⊞ I.cocomplex ⟶ _).f (n + 1)) := by
      rw [← HomologicalComplex.comp_f, biprod.lift_fst]
      infer_instance
    exact mono_of_mono _ ((biprod.fst : embeddingComplex K ⊞ I.cocomplex ⟶ _).f (n + 1))

include hinj hP hF hK in
/-- **Resolutions in an adapted class compute right derived functors.** Let `P` be a class of
objects containing the injective objects, closed under isomorphisms and under cokernels of
monomorphisms, on whose short exact sequences `F` is exact. If `ι : X[0] ⟶ K` is a resolution of
`X` by objects of `P` and `φ : K ⟶ I` is compatible with `ι` and an injective resolution `I` of
`X`, then `F(φ) : F(K) ⟶ F(I)` is a quasi-isomorphism. -/
theorem quasiIso_map_of_comp_eq (I : InjectiveResolution X) (φ : K ⟶ I.cocomplex)
    (hφ : ι ≫ φ = I.ι) : QuasiIso ((F.mapHomologicalComplex _).map φ) := by
  -- `φ` factors as `K ⟶ T ⊞ I ⟶ I` through the degreewise monomorphism `ψ = (χ, φ)`
  let T := embeddingComplex K
  let ψ : K ⟶ T ⊞ I.cocomplex := biprod.lift (toEmbeddingComplex K) φ
  have hψ : ψ ≫ biprod.snd = φ := biprod.lift_snd _ _
  have : Mono ψ := mono_lift_toEmbeddingComplex ι φ hφ
  have hsplit := ShortComplex.Splitting.ofHasBinaryBiproduct T I.cocomplex
  have : QuasiIso (biprod.snd : T ⊞ I.cocomplex ⟶ I.cocomplex) :=
    hsplit.shortExact.quasiIso_g_iff.2 (Homotopy.acyclic (embeddingComplexHomotopy K))
  have : QuasiIso φ := by
    have : QuasiIso (ι ≫ φ) := by rw [hφ]; infer_instance
    exact quasiIso_of_comp_left ι φ
  have : QuasiIso ψ := by
    have : QuasiIso (ψ ≫ biprod.snd) := by rw [hψ]; infer_instance
    exact quasiIso_of_comp_right ψ biprod.snd
  -- the cokernel `Q` of `ψ` is acyclic with terms in `P`, so `F` keeps `0 ⟶ K ⟶ T ⊞ I ⟶ Q ⟶ 0`
  -- short exact and `F(Q)` acyclic
  let S := ShortComplex.mk ψ (cokernel.π ψ) (cokernel.condition ψ)
  have hS : S.ShortExact := ShortComplex.ShortExact.mk'
    (ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel ψ)) inferInstance inferInstance
  have hSn := (HomologicalComplex.shortExact_iff_degreewise_shortExact S).1 hS
  have hX₂ (n : ℕ) : P (S.X₂.X n) :=
    hinj _ (Injective.of_iso (HomologicalComplex.biprodXIso T I.cocomplex n).symm inferInstance)
  have hFS : (S.map (F.mapHomologicalComplex _)).ShortExact :=
    HomologicalComplex.shortExact_of_degreewise_shortExact _ fun n ↦
      hF _ (hSn n) (hK n) (hX₂ n)
  have : QuasiIso ((F.mapHomologicalComplex _).map ψ) :=
    hFS.quasiIso_f_iff.2 (HomologicalComplex.Acyclic.map_of_shortExact F P hP hF
      (hS.quasiIso_f_iff.1 inferInstance) fun n ↦ hP _ (hSn n) (hK n) (hX₂ n))
  -- `F(T ⊞ I) ⟶ F(I)` is a quasi-isomorphism, as `F(T)` is acyclic
  have : QuasiIso ((F.mapHomologicalComplex _).map (biprod.snd : T ⊞ I.cocomplex ⟶ _)) :=
    (hsplit.map (F.mapHomologicalComplex _)).shortExact.quasiIso_g_iff.2
      (acyclic_map_embeddingComplex K F)
  rw [← hψ, Functor.map_comp]
  infer_instance

end Comparison

end CategoryTheory.InjectiveResolution

namespace CategoryTheory.Functor

open CochainComplex

variable {C : Type u₁} [Category.{v₁} C] [Abelian C] {D : Type u₂} [Category.{v₂} D] [Abelian D]
  [EnoughInjectives C] (F : C ⥤ D) [F.Additive] (P : ObjectProperty C)
  [P.IsClosedUnderIsomorphisms] (hinj : ∀ (Y : C), Injective Y → P Y)
  (hP : ∀ S : ShortComplex C, S.ShortExact → P S.X₁ → P S.X₂ → P S.X₃)
  (hF : ∀ S : ShortComplex C, S.ShortExact → P S.X₁ → P S.X₂ → (S.map F).ShortExact)
  {X : C} {K : CochainComplex C ℕ} (ι : (single₀ C).obj X ⟶ K) [QuasiIso ι]
  (hK : ∀ n, P (K.X n))

include hinj hP hF hK in
/-- **Right derived functors from adapted resolutions.** For a resolution `ι : X[0] ⟶ K` of `X`
by objects of a class `P` adapted to `F` (see
`CategoryTheory.InjectiveResolution.quasiIso_map_of_comp_eq`), `RⁿF(X) ≅ Hⁿ(F(K))`. It is
induced by `F` applied to the comparison map from `K` to any injective resolution of `X`
(`CategoryTheory.Functor.rightDerivedObjIsoOfResolution_hom_comp_homologyMap`). -/
noncomputable def rightDerivedObjIsoOfResolution (n : ℕ) :
    (F.rightDerived n).obj X ≅
      (HomologicalComplex.homologyFunctor D _ n).obj ((F.mapHomologicalComplex _).obj K) :=
  have := InjectiveResolution.quasiIso_map_of_comp_eq F P hinj hP hF ι hK (injectiveResolution X)
    (InjectiveResolution.descOfQuasiIso (𝟙 X) (injectiveResolution X) ι) (by simp)
  (injectiveResolution X).isoRightDerivedObj F n ≪≫
    (isoOfQuasiIsoAt ((F.mapHomologicalComplex _).map
      (InjectiveResolution.descOfQuasiIso (𝟙 X) (injectiveResolution X) ι)) n).symm

/-- The isomorphism `rightDerivedObjIsoOfResolution` is compatible with the identification of
`RⁿF(X)` through any injective resolution `I` of `X` and any comparison map `φ : K ⟶ I`. -/
@[reassoc]
lemma rightDerivedObjIsoOfResolution_hom_comp_homologyMap (n : ℕ) (I : InjectiveResolution X)
    (φ : K ⟶ I.cocomplex) (hφ : ι ≫ φ = I.ι) :
    (F.rightDerivedObjIsoOfResolution P hinj hP hF ι hK n).hom ≫
      (F.mapHomologicalComplex _ ⋙ HomologicalComplex.homologyFunctor _ _ n).map φ =
        (I.isoRightDerivedObj F n).hom := by
  let φ₀ := InjectiveResolution.descOfQuasiIso (𝟙 X) (injectiveResolution X) ι
  let e := InjectiveResolution.desc (𝟙 X) I (injectiveResolution X)
  -- `φ` and `φ₀ ≫ e` are two comparison maps `K ⟶ I`, hence homotopic
  have h₁ : (F.mapHomologicalComplex _ ⋙ HomologicalComplex.homologyFunctor _ _ n).map φ =
      (F.mapHomologicalComplex _ ⋙ HomologicalComplex.homologyFunctor _ _ n).map (φ₀ ≫ e) :=
    (F.mapHomotopy (InjectiveResolution.homotopyOfQuasiIso ι φ (φ₀ ≫ e)
      (by simp [φ₀, e, hφ]))).homologyMap_eq n
  have h₂ := InjectiveResolution.isoRightDerivedObj_hom_naturality (𝟙 X) (injectiveResolution X) I
    e (InjectiveResolution.desc_commutes_zero _ _ _) F n
  rw [Functor.map_id, Category.id_comp] at h₂
  have := InjectiveResolution.quasiIso_map_of_comp_eq F P hinj hP hF ι hK _ φ₀ (by simp [φ₀])
  rw [h₁, h₂, Functor.map_comp]
  -- the composite `(isoOfQuasiIsoAt _ n).inv ≫ Hⁿ(F(φ₀))` cancels
  exact (Category.assoc _ _ _).trans
    (_ ≫= isoOfQuasiIsoAt_inv_hom_id_assoc ((F.mapHomologicalComplex _).map φ₀) n _)

/-- The computation by adapted resolutions is natural in a morphism of augmented resolutions.
The map on the resolutions need not be a quasi-isomorphism. -/
@[reassoc]
lemma rightDerivedObjIsoOfResolution_hom_naturality {Y : C} {L : CochainComplex C ℕ}
    (κ : (single₀ C).obj Y ⟶ L) [QuasiIso κ] (hL : ∀ n, P (L.X n))
    (f : X ⟶ Y) (φ : K ⟶ L) (hφ : ι ≫ φ = (single₀ C).map f ≫ κ) (n : ℕ) :
    (F.rightDerived n).map f ≫ (F.rightDerivedObjIsoOfResolution P hinj hP hF κ hL n).hom =
      (F.rightDerivedObjIsoOfResolution P hinj hP hF ι hK n).hom ≫
        (F.mapHomologicalComplex _ ⋙ HomologicalComplex.homologyFunctor _ _ n).map φ := by
  let I := injectiveResolution X
  let J := injectiveResolution Y
  let a := InjectiveResolution.descOfQuasiIso (𝟙 X) I ι
  let b := InjectiveResolution.descOfQuasiIso (𝟙 Y) J κ
  let c := InjectiveResolution.desc f J I
  have hb : QuasiIso ((F.mapHomologicalComplex _).map b) :=
    InjectiveResolution.quasiIso_map_of_comp_eq F P hinj hP hF κ hL J b (by simp [b])
  -- The two routes from K to J lift the same map f, hence induce the same homology map.
  have h : (F.mapHomologicalComplex _ ⋙ HomologicalComplex.homologyFunctor _ _ n).map
      (φ ≫ b) =
      (F.mapHomologicalComplex _ ⋙ HomologicalComplex.homologyFunctor _ _ n).map (a ≫ c) :=
    (F.mapHomotopy (InjectiveResolution.homotopyOfQuasiIso ι (φ ≫ b) (a ≫ c)
      (by simp [reassoc_of% hφ, a, b, c]))).homologyMap_eq n
  have : IsIso
      ((F.mapHomologicalComplex _ ⋙ HomologicalComplex.homologyFunctor _ _ n).map b) :=
    inferInstanceAs (IsIso (HomologicalComplex.homologyMap
      ((F.mapHomologicalComplex _).map b) n))
  -- After the comparison from L to J, naturality is the native injective-resolution formula.
  apply (cancel_mono
    ((F.mapHomologicalComplex _ ⋙ HomologicalComplex.homologyFunctor _ _ n).map b)).1
  rw [Category.assoc, rightDerivedObjIsoOfResolution_hom_comp_homologyMap
    F P hinj hP hF κ hL n J b (by simp [b])]
  rw [Category.assoc, ← Functor.map_comp, h, Functor.map_comp, ← Category.assoc,
    rightDerivedObjIsoOfResolution_hom_comp_homologyMap
      F P hinj hP hF ι hK n I a (by simp [a])]
  exact InjectiveResolution.isoRightDerivedObj_hom_naturality f I J c
    (InjectiveResolution.desc_commutes_zero f J I) F n

/-- A functorial resolution by objects of a class adapted to `F` computes `RⁿF`, naturally in
its argument. The components are the comparisons through arbitrary injective resolutions given
by `rightDerivedObjIsoOfResolution_hom_comp_homologyMap`. -/
noncomputable def rightDerivedIsoOfResolution (K : C ⥤ CochainComplex C ℕ)
    (ι : single₀ C ⟶ K) [∀ X, QuasiIso (ι.app X)] (hK : ∀ X n, P ((K.obj X).X n)) (n : ℕ) :
    F.rightDerived n ≅ K ⋙ F.mapHomologicalComplex _ ⋙ HomologicalComplex.homologyFunctor _ _ n :=
  NatIso.ofComponents (fun X ↦ F.rightDerivedObjIsoOfResolution P hinj hP hF (ι.app X) (hK X) n)
    (fun f ↦ F.rightDerivedObjIsoOfResolution_hom_naturality P hinj hP hF
      (ι.app _) (hK _) (ι.app _) (hK _) f (K.map f) (ι.naturality f).symm n)

/-- Components of the natural comparison are the comparisons for the individual resolutions. -/
@[simp]
lemma rightDerivedIsoOfResolution_app (K : C ⥤ CochainComplex C ℕ)
    (ι : single₀ C ⟶ K) [∀ X, QuasiIso (ι.app X)] (hK : ∀ X n, P ((K.obj X).X n))
    (n : ℕ) (X : C) :
    (F.rightDerivedIsoOfResolution P hinj hP hF K ι hK n).app X =
      F.rightDerivedObjIsoOfResolution P hinj hP hF (ι.app X) (hK X) n :=
  (rfl)

end CategoryTheory.Functor
