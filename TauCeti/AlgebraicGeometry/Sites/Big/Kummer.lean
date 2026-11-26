/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.FiniteEtale.Kummer
public import TauCeti.AlgebraicGeometry.Sites.Big.StructureSheaf
public import TauCeti.AlgebraicGeometry.Sites.Fpqc
public import TauCeti.CategoryTheory.Sites.Over.Pullback
public import TauCeti.CategoryTheory.Sites.ShortExact

/-!
# The Kummer sequence on the big étale site

Let `S` be a scheme and `n` a natural number invertible on `S`. This file proves that the
sequence `0 → μ_n → 𝔾_m → 𝔾_m → 0`, whose second map is the `n`-th power map, is exact on the big
étale site `Over S` (Stacks, Lemma 59.28.1 (03PL)): `μ_n` is the kernel of the `n`-th power map,
and the `n`-th power map is an epimorphism of étale sheaves.

The kernel part holds on every site coarser than the fpqc site
(`AlgebraicGeometry.Scheme.isLimitMuKernelForkMap`, in
`TauCeti.AlgebraicGeometry.Sites.Big.StructureSheaf`). The surjectivity is étale
local: a unit `s` of `Γ(T, 𝒪_T)` acquires an `n`-th root on the Kummer cover
`Spec R[x]/(x ^ n - s) ⟶ Spec R` of each affine open `Spec R` of `T`
(`TauCeti.FiniteEtaleScheme.kummerCover`), which is a finite étale surjection because `n` is
invertible. These covers together form an étale cover of `T`
(`AlgebraicGeometry.Scheme.exists_etale_cover_pow_eq`). The surjectivity statements hold for
every topology finer than the étale topology, and the sheaf statements for every such topology
coarser than the fpqc topology, such as the étale topology itself.

The two parts assemble into the Kummer sequence `AlgebraicGeometry.Scheme.kummerSequence`, a
short exact sequence of sheaves of abelian groups (`kummerSequence_shortExact`). The big étale
site is too large for sheafification into abelian groups of the same universe, so its sheaves are
not known to form an abelian category; exactness instead uses that a locally surjective morphism
of abelian sheaves is the cokernel of its kernel
(`CategoryTheory.ShortComplex.shortExact_of_isLocallySurjective`). The Kummer sequence is
compatible with change of base: along `f : T ⟶ S` it restricts to the Kummer sequence of `T`
(`kummerSequenceOverMapPullbackIso`).

## Main results

* `AlgebraicGeometry.Scheme.exists_etale_cover_pow_eq`: if `n` is invertible on a scheme `X`, every
  unit of `Γ(X, 𝒪_X)` is an `n`-th power on the members of some étale cover of `X`.
* `AlgebraicGeometry.Scheme.isLocallySurjective_powHom`: for `n` invertible on `S`, the `n`-th power
  map of `𝔾_m` is locally surjective for every topology on schemes finer than the étale topology.
* `AlgebraicGeometry.Scheme.epi_sheafPushforwardContinuous_map_powHom`: for `n` invertible on `S`,
  the `n`-th power map of `𝔾_m`, regarded as a map of sheaves for such a topology coarser than
  the fpqc topology, for instance the étale topology, is an epimorphism.
* `AlgebraicGeometry.Scheme.kummerSequence`: the Kummer sequence `0 → μ_n → 𝔾_m → 𝔾_m → 0` on
  the site `Over S` for a topology coarser than the fpqc topology.
* `AlgebraicGeometry.Scheme.kummerSequence_shortExact`: for `n` invertible on `S` and a topology
  between the étale and the fpqc topology, the Kummer sequence is short exact.
* `AlgebraicGeometry.Scheme.kummerSequenceOverMapPullbackIso`: the restriction of the Kummer
  sequence of `S` along `f : T ⟶ S` is the Kummer sequence of `T`, so it is short exact as well
  (`kummerSequence_map_overMapPullback_shortExact`).

## References

* [Stacks Project, Lemma 59.28.1 (03PL)](https://stacks.math.columbia.edu/tag/03PL)
-/

public section

open CategoryTheory Limits TauCeti.FiniteEtaleScheme

universe u

namespace AlgebraicGeometry.Scheme

/-- **Units have `n`-th roots étale locally.** If `n` is invertible on a scheme `X`, then every
unit `s` of `Γ(X, 𝒪_X)` becomes an `n`-th power on each member of some étale cover of `X`: the
Kummer covers that extract an `n`-th root of `s` over the affine opens of `X`. -/
@[stacks 03PL "surjectivity of the `n`-th power map"]
theorem exists_etale_cover_pow_eq {X : Scheme.{u}} {n : ℕ} (hn : IsUnit (n : Γ(X, ⊤)))
    (s : Γ(X, ⊤)ˣ) :
    ∃ 𝒰 : Cover.{u} (precoverage @Etale) X, ∀ i, ∃ v : Γ(𝒰.X i, ⊤)ˣ,
      v ^ n = Units.map (𝒰.f i).appTop.hom.toMonoidHom s := by
  let 𝒱 := X.affineOpenCover
  -- The restriction of global sections to the affine open `Spec (𝒱.X i)`.
  let φ (i : 𝒱.I₀) : Γ(X, ⊤) ⟶ 𝒱.X i := (𝒱.f i).appTop ≫ (ΓSpecIso (𝒱.X i)).hom
  have hn' (i : 𝒱.I₀) : IsUnit (n : 𝒱.X i) := by simpa using hn.map (φ i).hom
  let K (i : 𝒱.I₀) := kummerCover (Units.map (φ i).hom.toMonoidHom s) n (hn' i)
  let 𝒰 : Cover.{u} (precoverage @Etale) X :=
    Cover.mkOfCovers 𝒱.I₀ (fun i ↦ (K i).obj.left) (fun i ↦ (K i).obj.hom ≫ 𝒱.f i)
      (fun x ↦ by
        obtain ⟨i, y, rfl⟩ := 𝒱.openCover.exists_eq x
        obtain ⟨z, rfl⟩ := (K i).obj.hom.surjective y
        exact ⟨i, z, rfl⟩)
      fun _ ↦ inferInstance
  refine ⟨𝒰, fun (i : 𝒱.I₀) ↦ ?_⟩
  obtain ⟨v, hv⟩ := exists_pow_eq_kummerCover_appTop _ n (hn' i)
  refine ⟨v, hv.trans (Units.ext ?_)⟩
  simp only [φ, CommRingCat.hom_comp, RingHom.toMonoidHom_eq_coe, Units.coe_map,
    MonoidHom.coe_ofClass, RingHom.coe_comp, Function.comp_apply, Iso.hom_inv_id_apply]
  -- `𝒰.f i` is by definition the composite `(K i).obj.hom ≫ 𝒱.f i`.
  exact (congr($(Hom.comp_appTop (K i).obj.hom (𝒱.f i)) (s : Γ(X, ⊤)))).symm

variable (S : Scheme.{u}) {n : ℕ}

/-- A morphism `f : T' ⟶ T` of the big site lies in the image sieve of the `n`-th power map at
a unit `s` on `T` as soon as the pullback of `s` along `f` is an `n`-th power. -/
private lemma imageSieve_powHom_arrows {T T' : Over S} (f : T' ⟶ T)
    (s : Additive Γ(T.left, ⊤)ˣ) (v : Γ(T'.left, ⊤)ˣ)
    (hv : v ^ n = Units.map f.left.appTop.hom.toMonoidHom s.toMul) :
    Presheaf.imageSieve (powHom S n).hom (F := (Gm S).obj) (G := (Gm S).obj) s f :=
  ⟨Additive.ofMul v, (powHom_app_apply S n T' (Additive.ofMul v)).trans
    ((congrArg Additive.ofMul hv).trans (Gm_map_apply S f s).symm)⟩

/-- **The `n`-th power map of `𝔾_m` is étale locally surjective.** For `n` invertible on `S`, the
`n`-th power map `𝔾_m ⟶ 𝔾_m` on the big site `Over S` is locally surjective for every topology on
schemes finer than the étale topology. -/
theorem isLocallySurjective_powHom {J : GrothendieckTopology Scheme.{u}}
    (hJ : etaleTopology ≤ J) (hn : IsUnit (n : Γ(S, ⊤))) :
    Presheaf.IsLocallySurjective (J.over S) (powHom S n).hom where
  imageSieve_mem {T} s := by
    have hnT : IsUnit (n : Γ(T.left, ⊤)) := by simpa using hn.map T.hom.appTop.hom
    obtain ⟨𝒰, h𝒰⟩ := exists_etale_cover_pow_eq hnT s.toMul
    refine hJ _ (etaleTopology.superset_covering ?_ 𝒰.mem_grothendieckTopology)
    rw [Sieve.ofArrows, Sieve.generate_le_iff]
    rintro _ _ ⟨i⟩
    obtain ⟨v, hv⟩ := h𝒰 i
    rw [Sieve.overEquiv_iff]
    exact imageSieve_powHom_arrows S _ s v hv

/-- **Surjectivity in the Kummer sequence.** For `n` invertible on `S` and a topology `J` on
schemes between the étale and the fpqc topology, such as the étale topology itself, the `n`-th
power map `𝔾_m ⟶ 𝔾_m`, regarded as a map of sheaves on the site `Over S` for `J`, is an
epimorphism. -/
@[stacks 03PL]
theorem epi_sheafPushforwardContinuous_map_powHom {J : GrothendieckTopology Scheme.{u}}
    [(𝟭 (Over S)).IsContinuous (J.over S) (fpqcTopology.over S)]
    (hJ : etaleTopology ≤ J) (hn : IsUnit (n : Γ(S, ⊤))) :
    Epi (((𝟭 (Over S)).sheafPushforwardContinuous AddCommGrpCat.{u} (J.over S)
      (fpqcTopology.over S)).map (powHom S n)) :=
  have : Sheaf.IsLocallySurjective (((𝟭 (Over S)).sheafPushforwardContinuous AddCommGrpCat.{u}
      (J.over S) (fpqcTopology.over S)).map (powHom S n)) :=
    isLocallySurjective_powHom S hJ hn
  inferInstance

section KummerSequence

variable (J : GrothendieckTopology Scheme.{u})
  [(𝟭 (Over S)).IsContinuous (J.over S) (fpqcTopology.over S)] (n : ℕ)

/-- **The Kummer sequence** `0 → μ_n → 𝔾_m → 𝔾_m → 0` of `S`, whose second map is the `n`-th
power map, as a complex of sheaves of abelian groups on the site `Over S` for a topology `J` on
schemes coarser than the fpqc topology, such as the étale topology. It is short exact when `n` is
invertible on `S` and `J` is finer than the étale topology (`kummerSequence_shortExact`). -/
@[expose]
noncomputable def kummerSequence : ShortComplex (Sheaf (J.over S) AddCommGrpCat.{u}) :=
  (ShortComplex.mk (muToGm S n) (powHom S n) (muToGm_comp_powHom S n)).map
    ((𝟭 (Over S)).sheafPushforwardContinuous AddCommGrpCat.{u} (J.over S) (fpqcTopology.over S))

@[simp]
lemma kummerSequence_X₁ : (kummerSequence S J n).X₁ =
    ((𝟭 (Over S)).sheafPushforwardContinuous AddCommGrpCat.{u} (J.over S)
      (fpqcTopology.over S)).obj (mu S n) :=
  (rfl)

@[simp]
lemma kummerSequence_X₂ : (kummerSequence S J n).X₂ =
    ((𝟭 (Over S)).sheafPushforwardContinuous AddCommGrpCat.{u} (J.over S)
      (fpqcTopology.over S)).obj (Gm S) :=
  (rfl)

@[simp]
lemma kummerSequence_X₃ : (kummerSequence S J n).X₃ =
    ((𝟭 (Over S)).sheafPushforwardContinuous AddCommGrpCat.{u} (J.over S)
      (fpqcTopology.over S)).obj (Gm S) :=
  (rfl)

@[simp]
lemma kummerSequence_f : (kummerSequence S J n).f =
    ((𝟭 (Over S)).sheafPushforwardContinuous AddCommGrpCat.{u} (J.over S)
      (fpqcTopology.over S)).map (muToGm S n) :=
  (rfl)

@[simp]
lemma kummerSequence_g : (kummerSequence S J n).g =
    ((𝟭 (Over S)).sheafPushforwardContinuous AddCommGrpCat.{u} (J.over S)
      (fpqcTopology.over S)).map (powHom S n) :=
  (rfl)

/-- **The Kummer sequence is exact.** For `n` invertible on `S` and a topology `J` on schemes
between the étale and the fpqc topology, such as the étale topology itself, the Kummer sequence
`0 → μ_n → 𝔾_m → 𝔾_m → 0` is a short exact sequence of sheaves of abelian groups on the site
`Over S` for `J`. -/
@[stacks 03PL]
theorem kummerSequence_shortExact (hJ : etaleTopology ≤ J) (hn : IsUnit (n : Γ(S, ⊤))) :
    (kummerSequence S J n).ShortExact := by
  have : Sheaf.IsLocallySurjective (kummerSequence S J n).g := isLocallySurjective_powHom S hJ hn
  -- The kernel fork of `kummerSequence` is the image of the kernel fork of `μ_n` on the fpqc site.
  exact ShortComplex.shortExact_of_isLocallySurjective (isLimitMuKernelForkMap S J n)

variable {S} {T : Scheme.{u}} (f : T ⟶ S)
  [(𝟭 (Over T)).IsContinuous (J.over T) (fpqcTopology.over T)]

/-- The Kummer complex `μ_n ⟶ 𝔾_m ⟶ 𝔾_m` on the big fpqc site of `S` restricts, along
`f : T ⟶ S`, to the Kummer complex on the big fpqc site of `T`. -/
private noncomputable def fpqcKummerOverMapPullbackIso :
    (ShortComplex.mk (muToGm S n) (powHom S n) (muToGm_comp_powHom S n)).map
        (fpqcTopology.overMapPullback AddCommGrpCat.{u} f) ≅
      ShortComplex.mk (muToGm T n) (powHom T n) (muToGm_comp_powHom T n) :=
  ShortComplex.isoMk (muOverMapPullbackIso f n) (GmOverMapPullbackIso f) (GmOverMapPullbackIso f)
    (muOverMapPullbackIso_hom_comp_muToGm f n) (GmOverMapPullbackIso_hom_comp_powHom f n)

/-- **The Kummer sequence restricts to the Kummer sequence.** For a morphism `f : T ⟶ S`, the
restriction of the Kummer sequence of `S` along `f`, from the site `Over S` to the site `Over T`
(the slice of `Over S` at `T`), is the Kummer sequence of `T`. -/
noncomputable def kummerSequenceOverMapPullbackIso :
    (kummerSequence S J n).map (J.overMapPullback AddCommGrpCat.{u} f) ≅
      kummerSequence T J n :=
  -- Regarding fpqc sheaves as `J`-sheaves commutes with the restriction along `f`, and the
  -- restriction of the fpqc Kummer complex of `S` is that of `T`.
  (ShortComplex.mk (muToGm S n) (powHom S n) (muToGm_comp_powHom S n)).mapNatIso
      (J.sheafPushforwardContinuousIdCompOverMapPullbackIso fpqcTopology AddCommGrpCat.{u} f) ≪≫
    ((𝟭 (Over T)).sheafPushforwardContinuous AddCommGrpCat.{u} (J.over T)
      (fpqcTopology.over T)).mapShortComplex.mapIso (fpqcKummerOverMapPullbackIso n f)

@[simp]
lemma kummerSequenceOverMapPullbackIso_hom_τ₁ :
    (kummerSequenceOverMapPullbackIso J n f).hom.τ₁ =
      ((𝟭 (Over T)).sheafPushforwardContinuous AddCommGrpCat.{u} (J.over T)
        (fpqcTopology.over T)).map (muOverMapPullbackIso f n).hom := by
  unfold kummerSequenceOverMapPullbackIso kummerSequence
  simp only [ShortComplex.map_X₁, ShortComplex.map_comp, Iso.trans_hom,
    ShortComplex.mapNatIso_hom, Functor.mapIso_hom, ShortComplex.comp_τ₁,
    ShortComplex.mapNatTrans_τ₁,
    GrothendieckTopology.sheafPushforwardContinuousIdCompOverMapPullbackIso_hom_app,
    Functor.comp_obj, Functor.mapShortComplex_map_τ₁]
  exact Category.id_comp _

@[simp]
lemma kummerSequenceOverMapPullbackIso_hom_τ₂ :
    (kummerSequenceOverMapPullbackIso J n f).hom.τ₂ =
      ((𝟭 (Over T)).sheafPushforwardContinuous AddCommGrpCat.{u} (J.over T)
        (fpqcTopology.over T)).map (GmOverMapPullbackIso f).hom := by
  unfold kummerSequenceOverMapPullbackIso kummerSequence
  simp only [ShortComplex.map_X₂, ShortComplex.map_comp, Iso.trans_hom,
    ShortComplex.mapNatIso_hom, Functor.mapIso_hom, ShortComplex.comp_τ₂,
    ShortComplex.mapNatTrans_τ₂,
    GrothendieckTopology.sheafPushforwardContinuousIdCompOverMapPullbackIso_hom_app,
    Functor.comp_obj, Functor.mapShortComplex_map_τ₂]
  exact Category.id_comp _

@[simp]
lemma kummerSequenceOverMapPullbackIso_hom_τ₃ :
    (kummerSequenceOverMapPullbackIso J n f).hom.τ₃ =
      ((𝟭 (Over T)).sheafPushforwardContinuous AddCommGrpCat.{u} (J.over T)
        (fpqcTopology.over T)).map (GmOverMapPullbackIso f).hom := by
  unfold kummerSequenceOverMapPullbackIso kummerSequence
  simp only [ShortComplex.map_X₃, ShortComplex.map_comp, Iso.trans_hom,
    ShortComplex.mapNatIso_hom, Functor.mapIso_hom, ShortComplex.comp_τ₃,
    ShortComplex.mapNatTrans_τ₃,
    GrothendieckTopology.sheafPushforwardContinuousIdCompOverMapPullbackIso_hom_app,
    Functor.comp_obj, Functor.mapShortComplex_map_τ₃]
  exact Category.id_comp _

@[simp]
lemma kummerSequenceOverMapPullbackIso_inv_τ₁ :
    (kummerSequenceOverMapPullbackIso J n f).inv.τ₁ =
      ((𝟭 (Over T)).sheafPushforwardContinuous AddCommGrpCat.{u} (J.over T)
        (fpqcTopology.over T)).map (muOverMapPullbackIso f n).inv := by
  unfold kummerSequenceOverMapPullbackIso kummerSequence
  simp only [ShortComplex.map_X₁, ShortComplex.map_comp, Iso.trans_inv,
    Functor.mapIso_inv, ShortComplex.mapNatIso_inv, ShortComplex.comp_τ₁,
    Functor.mapShortComplex_map_τ₁, ShortComplex.mapNatTrans_τ₁,
    GrothendieckTopology.sheafPushforwardContinuousIdCompOverMapPullbackIso_inv_app,
    Functor.comp_obj]
  exact Category.comp_id _

@[simp]
lemma kummerSequenceOverMapPullbackIso_inv_τ₂ :
    (kummerSequenceOverMapPullbackIso J n f).inv.τ₂ =
      ((𝟭 (Over T)).sheafPushforwardContinuous AddCommGrpCat.{u} (J.over T)
        (fpqcTopology.over T)).map (GmOverMapPullbackIso f).inv := by
  unfold kummerSequenceOverMapPullbackIso kummerSequence
  simp only [ShortComplex.map_X₂, ShortComplex.map_comp, Iso.trans_inv,
    Functor.mapIso_inv, ShortComplex.mapNatIso_inv, ShortComplex.comp_τ₂,
    Functor.mapShortComplex_map_τ₂, ShortComplex.mapNatTrans_τ₂,
    GrothendieckTopology.sheafPushforwardContinuousIdCompOverMapPullbackIso_inv_app,
    Functor.comp_obj]
  exact Category.comp_id _

@[simp]
lemma kummerSequenceOverMapPullbackIso_inv_τ₃ :
    (kummerSequenceOverMapPullbackIso J n f).inv.τ₃ =
      ((𝟭 (Over T)).sheafPushforwardContinuous AddCommGrpCat.{u} (J.over T)
        (fpqcTopology.over T)).map (GmOverMapPullbackIso f).inv := by
  unfold kummerSequenceOverMapPullbackIso kummerSequence
  simp only [ShortComplex.map_X₃, ShortComplex.map_comp, Iso.trans_inv,
    Functor.mapIso_inv, ShortComplex.mapNatIso_inv, ShortComplex.comp_τ₃,
    Functor.mapShortComplex_map_τ₃, ShortComplex.mapNatTrans_τ₃,
    GrothendieckTopology.sheafPushforwardContinuousIdCompOverMapPullbackIso_inv_app,
    Functor.comp_obj]
  exact Category.comp_id _

/-- **The restricted Kummer sequence is exact.** For a morphism `f : T ⟶ S`, a natural number `n`
invertible on `T` (for instance, invertible on `S`) and a topology `J` on schemes between the
étale and the fpqc topology, the restriction of the Kummer sequence of `S` along `f` to the site
`Over T` is short exact. -/
theorem kummerSequence_map_overMapPullback_shortExact (hJ : etaleTopology ≤ J)
    (hn : IsUnit (n : Γ(T, ⊤))) :
    ((kummerSequence S J n).map (J.overMapPullback AddCommGrpCat.{u} f)).ShortExact :=
  ShortComplex.shortExact_of_iso (kummerSequenceOverMapPullbackIso J n f).symm
    (kummerSequence_shortExact T J n hJ hn)

end KummerSequence

end AlgebraicGeometry.Scheme
