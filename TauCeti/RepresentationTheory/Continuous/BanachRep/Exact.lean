/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Exact.ExactStructure
public import TauCeti.RepresentationTheory.Continuous.BanachRep.Basic
import TauCeti.Topology.Algebra.Module.ContinuousLinearMap.Exact

/-!
# The strict exact structure on Banach representations

A short complex `0 → X₁ → X₂ → X₃ → 0` of Banach representations is a *conflation* when it is
algebraically exact: the first map is injective, the second is surjective, and the image of the
first is the kernel of the second. By the open mapping theorem such a sequence is automatically
strict: the first map is a homeomorphism onto the closed kernel of the second, and the second is
an open surjection. These conflations form a Quillen exact structure on `TauCeti.BanachRep 𝕜 G`.
This is the exact structure in which extensions of Banach Galois representations, and later the
extension groups of almost `C`-representations, are formed.

The inflations are the injective morphisms with closed range and the deflations are the surjective
morphisms. Pullbacks of arbitrary pairs of morphisms exist: they are closed invariant subspaces of
the product. The pushout of an inflation `i : A ⟶ A'` along `f : A ⟶ B` is the quotient of
`B × A'` by the image of `a ↦ (f a, -i a)`, which is closed because `i` is antilipschitz.

## Main definitions

* `TauCeti.BanachRep.exactStructure`: the exact structure of algebraically exact sequences.
* `TauCeti.BanachRep` has pullbacks, built inside the product.

## Main results

* `TauCeti.BanachRep.isLimitKernelForkOfExact`, `TauCeti.BanachRep.isColimitCokernelCoforkOfExact`:
  an algebraically exact sequence is a kernel and a cokernel sequence.
* `TauCeti.BanachRep.exactStructure_conflation_iff`: the conflations are the algebraically exact
  sequences.
* `TauCeti.BanachRep.exactStructure_isInflation_iff`: the inflations are the injective morphisms
  with closed range.
* `TauCeti.BanachRep.exactStructure_isDeflation_iff`: the deflations are the surjective morphisms.
* `TauCeti.BanachRep.isClosedEmbedding_of_isInflation`,
  `TauCeti.BanachRep.isOpenQuotientMap_of_isDeflation`: conflations are strict.

## References

* J.-M. Fontaine, *Presque `C_p`-représentations*, Documenta Mathematica, Extra Volume Kato
  (2003), 285–385, §1.2.
* P. Colmez and W. Nizioł, *On the cohomology of `p`-adic analytic spaces, II: The
  `C_st`-conjecture* (2025), §2.1.
* T. Bühler, *Exact categories*, Expositiones Mathematicae **28** (2010), 1–69, Definition 2.1.
-/

public section

universe w u v

open CategoryTheory CategoryTheory.Limits Topology

namespace TauCeti

namespace BanachRep

variable {𝕜 : Type u} [NontriviallyNormedField 𝕜] {G : Type v} [Monoid G] [TopologicalSpace G]
  {X Y Z : BanachRep.{w} 𝕜 G}

/-! ### Exact sequences are kernel and cokernel sequences -/

section KernelCokernel

variable {f : X ⟶ Y} {g : Y ⟶ Z}

/-- **An injective morphism whose range is the kernel of `g` is a kernel of `g`.** The lift of a
morphism killed by `g` is continuous by the open mapping theorem. -/
noncomputable def isLimitKernelForkOfExact (w : f ≫ g = 0) (hf : Function.Injective f.hom)
    (hfg : Function.Exact f.hom g.hom) : IsLimit (KernelFork.ofι f w) :=
  haveI := mono_of_injective f hf
  let e := f.hom.equivRange hf hfg.isClosed_range
  KernelFork.IsLimit.ofι' f w fun {T} k hk =>
    have hmem : ∀ t, k.hom t ∈ LinearMap.range (f.hom : X →ₗ[𝕜] Y) := fun t =>
      (hfg (k.hom t)).mp congr(($hk).hom t)
    let l : T →L[𝕜] X := e.symm.toContinuousLinearMap.comp (k.hom.codRestrict _ hmem)
    have hl : ∀ t, f.hom (l t) = k.hom t := fun t =>
      congr(Subtype.val $(e.apply_symm_apply ⟨k.hom t, hmem t⟩))
    ⟨⟨l, fun g t => hf (by simp [hl])⟩, hom_ext (ContinuousLinearMap.ext hl)⟩

/-- **A surjective morphism whose kernel is the range of `f` is a cokernel of `f`.** The descent
of a morphism killing `f` is continuous because, by the open mapping theorem, `g` is a quotient
map. -/
noncomputable def isColimitCokernelCoforkOfExact (w : f ≫ g = 0)
    (hg : Function.Surjective g.hom) (hfg : Function.Exact f.hom g.hom) :
    IsColimit (CokernelCofork.ofπ g w) :=
  haveI := epi_of_surjective g hg
  have hq : IsQuotientMap g.hom := g.hom.isQuotientMap hg
  CokernelCofork.IsColimit.ofπ' g w fun {T} k hk =>
    -- `Z` is the quotient of `Y` by the range of `f`, and `k` kills that range.
    let e := Function.Exact.linearEquivOfSurjective (f := (f.hom : X →ₗ[𝕜] Y))
      (g := (g.hom : Y →ₗ[𝕜] Z)) hfg hg
    have hkf : (k.hom : Y →ₗ[𝕜] T).comp (f.hom : X →ₗ[𝕜] Y) = 0 :=
      LinearMap.ext fun x => by simpa using congr(($hk).hom x)
    let l : Z →ₗ[𝕜] T := ((LinearMap.range (f.hom : X →ₗ[𝕜] Y)).liftQ k.hom
      (LinearMap.range_le_ker_iff.mpr hkf)).comp e.symm.toLinearMap
    have hl : ∀ y, l (g.hom y) = k.hom y := fun y => by
      have h : e.symm (g.hom y) = Submodule.Quotient.mk y :=
        Function.Exact.linearEquivOfSurjective_symm_apply hfg hg y
      simp [l, h]
    have hlc : Continuous l := hq.continuous_iff.mpr (k.hom.continuous.congr fun y => (hl y).symm)
    ⟨⟨⟨l, hlc⟩, fun t z => by
      obtain ⟨y, rfl⟩ := hg z
      rw [ContinuousLinearMap.coe_mk', ← g.hom_comm_apply, hl, hl, k.hom_comm_apply]⟩,
      hom_ext (ContinuousLinearMap.ext hl)⟩

end KernelCokernel

/-! ### The conflation class -/

/-- The predicate that a short complex of Banach representations is algebraically exact. -/
private def IsConflation (S : ShortComplex (BanachRep.{w} 𝕜 G)) : Prop :=
  Function.Injective S.f.hom ∧ Function.Surjective S.g.hom ∧ Function.Exact S.f.hom S.g.hom

private theorem isConflation_of_iso {S T : ShortComplex (BanachRep.{w} 𝕜 G)} (e : S ≅ T)
    (hS : IsConflation S) : IsConflation T := by
  obtain ⟨hf, hg, hfg⟩ := hS
  have h₁ := bijective_of_isIso e.hom.τ₁
  have h₂ := bijective_of_isIso e.hom.τ₂
  have h₃ := bijective_of_isIso e.hom.τ₃
  have c₁ : ∀ x, T.f.hom (e.hom.τ₁.hom x) = e.hom.τ₂.hom (S.f.hom x) := fun x => by
    simpa using congr(($(e.hom.comm₁₂)).hom x)
  have c₂ : ∀ y, T.g.hom (e.hom.τ₂.hom y) = e.hom.τ₃.hom (S.g.hom y) := fun y => by
    simpa using congr(($(e.hom.comm₂₃)).hom y)
  refine ⟨fun a b hab => ?_, fun z => ?_, ?_⟩
  · obtain ⟨a, rfl⟩ := h₁.2 a
    obtain ⟨b, rfl⟩ := h₁.2 b
    rw [c₁, c₁] at hab
    rw [hf (h₂.1 hab)]
  · obtain ⟨z, rfl⟩ := h₃.2 z
    obtain ⟨y, rfl⟩ := hg z
    exact ⟨_, c₂ y⟩
  · exact (LinearMap.exact_iff_of_surjective_of_bijective_of_injective _ _ _ _
      e.hom.τ₁.hom.toLinearMap e.hom.τ₂.hom.toLinearMap e.hom.τ₃.hom.toLinearMap
      (LinearMap.ext c₁) (LinearMap.ext c₂) h₁.2 h₂ h₃.1).mp hfg

/-- The conflation class of algebraically exact sequences. -/
private noncomputable def conflationClass : ConflationClass (BanachRep.{w} 𝕜 G) where
  Conflation := IsConflation
  isKernelCokernelPair _ hS :=
    ⟨⟨isLimitKernelForkOfExact _ hS.1 hS.2.2⟩, ⟨isColimitCokernelCoforkOfExact _ hS.2.1 hS.2.2⟩⟩
  isClosedUnderIsomorphisms := ⟨isConflation_of_iso⟩

private theorem conflationClass_isInflation_iff (i : X ⟶ Y) :
    conflationClass.IsInflation i ↔
      Function.Injective i.hom ∧ IsClosed (Set.range i.hom) := by
  rw [ConflationClass.isInflation_iff]
  refine ⟨fun ⟨_, _, _, hS⟩ => ⟨hS.1, hS.2.2.isClosed_range⟩, fun ⟨hi, hc⟩ => ?_⟩
  let W := LinearMap.range (i.hom : X →ₗ[𝕜] Y)
  have hW : ∀ (g : G), ∀ y ∈ W, Y.ρ g y ∈ W := range_invariant i
  refine ⟨quotient Y W hW hc, quotientπ Y W hW hc, hom_ext (ContinuousLinearMap.ext fun x => ?_),
    hi, quotientπ_surjective Y W hW hc, fun y => ?_⟩
  · rw [hom_comp, ContinuousLinearMap.comp_apply, hom_zero, _root_.zero_apply]
    exact (quotientπ_hom_apply_eq_zero_iff Y W hW hc _).mpr ⟨x, rfl⟩
  · exact quotientπ_hom_apply_eq_zero_iff Y W hW hc y

private theorem conflationClass_isDeflation_iff (p : X ⟶ Y) :
    conflationClass.IsDeflation p ↔ Function.Surjective p.hom := by
  rw [ConflationClass.isDeflation_iff]
  refine ⟨fun ⟨_, _, _, hS⟩ => hS.2.1, fun hp => ?_⟩
  let W := LinearMap.ker (p.hom : X →ₗ[𝕜] Y)
  have hW : ∀ (g : G), ∀ x ∈ W, X.ρ g x ∈ W := ker_invariant p
  refine ⟨subrepresentation X W hW p.hom.isClosed_ker, subrepresentationι X W hW p.hom.isClosed_ker,
    hom_ext (ContinuousLinearMap.ext fun x => by simp [W]),
    subrepresentationι_injective X W hW p.hom.isClosed_ker, hp, fun x => ?_⟩
  simp [W]

/-! ### Pullbacks -/

section Pullback

variable (f : X ⟶ Z) (g : Y ⟶ Z)

/-- The invariant closed subspace `{(x, y) | f x = g y}` of `X × Y`. -/
private noncomputable def pullbackSubmodule : Submodule 𝕜 (X × Y) :=
  LinearMap.ker ((f.hom.comp (ContinuousLinearMap.fst 𝕜 X Y) -
    g.hom.comp (ContinuousLinearMap.snd 𝕜 X Y) : X × Y →L[𝕜] Z) : X × Y →ₗ[𝕜] Z)

private theorem mem_pullbackSubmodule (x : prod X Y) :
    x ∈ pullbackSubmodule f g ↔ f.hom x.1 = g.hom x.2 := by
  simp [pullbackSubmodule, sub_eq_zero]

private theorem pullbackSubmodule_invariant :
    ∀ (t : G), ∀ x ∈ pullbackSubmodule f g, (prod X Y).ρ t x ∈ pullbackSubmodule f g := by
  intro t x hx
  rw [mem_pullbackSubmodule] at hx ⊢
  simp [hx]

private theorem isClosed_pullbackSubmodule : IsClosed (pullbackSubmodule f g : Set (prod X Y)) :=
  ContinuousLinearMap.isClosed_ker _

/-- The pullback object: the closed invariant subspace `{(x, y) | f x = g y}` of `X × Y`. -/
private noncomputable abbrev pullbackObj : BanachRep.{w} 𝕜 G :=
  subrepresentation (prod X Y) _ (pullbackSubmodule_invariant f g) (isClosed_pullbackSubmodule f g)

/-- The pullback square of `f` and `g`, with the two projections out of `pullbackObj f g`. -/
private noncomputable def pullbackCone : PullbackCone f g :=
  PullbackCone.mk (W := pullbackObj f g) (subrepresentationι _ _ _ _ ≫ prodFst X Y)
    (subrepresentationι _ _ _ _ ≫ prodSnd X Y)
    (hom_ext (ContinuousLinearMap.ext fun x => by
      simpa using (mem_pullbackSubmodule f g x).mp x.property))

private theorem pullbackCone_fst_hom_apply (x : pullbackObj f g) :
    (pullbackCone f g).fst.hom x = (x : prod X Y).1 := by
  -- `PullbackCone.mk` makes the first leg `subrepresentationι _ _ _ _ ≫ prodFst X Y`, but the cone
  -- point is `pullbackObj f g` only by unfolding `pullbackCone`, so `rw [PullbackCone.mk_fst]`
  -- cannot be used here.
  change (subrepresentationι _ _ _ _ ≫ prodFst X Y).hom x = _
  rw [hom_comp, ContinuousLinearMap.comp_apply, subrepresentationι_hom_apply, prodFst_hom_apply]

private theorem pullbackCone_snd_hom_apply (x : pullbackObj f g) :
    (pullbackCone f g).snd.hom x = (x : prod X Y).2 := by
  -- As for `pullbackCone_fst_hom_apply`, the second leg is `subrepresentationι ≫ prodSnd`.
  change (subrepresentationι _ _ _ _ ≫ prodSnd X Y).hom x = _
  rw [hom_comp, ContinuousLinearMap.comp_apply, subrepresentationι_hom_apply, prodSnd_hom_apply]

/-- The pullback cone of `f` and `g` is a limit. -/
private noncomputable def pullbackConeIsLimit : IsLimit (pullbackCone f g) :=
  PullbackCone.IsLimit.mk (pullbackCone f g).condition
    (fun s => subrepresentationLift (prod X Y) _ (pullbackSubmodule_invariant f g)
      (isClosed_pullbackSubmodule f g) ⟨s.fst.hom.prod s.snd.hom, fun _ _ => by simp⟩ fun t =>
      (mem_pullbackSubmodule f g _).mpr congr(($(s.condition)).hom t))
    (fun _ => by ext; simp [pullbackCone]) (fun _ => by ext; simp [pullbackCone])
    (fun _ m h₁ h₂ => hom_ext (ContinuousLinearMap.ext fun t => Subtype.ext (Prod.ext
      ((pullbackCone_fst_hom_apply f g (m.hom t)).symm.trans <| by
        rw [← ContinuousLinearMap.comp_apply, ← hom_comp, h₁]
        refine Eq.trans ?_ (congrArg Prod.fst (subrepresentationLift_hom_apply _ _ _ _ _ _ t)).symm
        exact (congrArg Prod.fst (ContinuousLinearMap.prod_apply _ _ t)).symm)
      ((pullbackCone_snd_hom_apply f g (m.hom t)).symm.trans <| by
        rw [← ContinuousLinearMap.comp_apply, ← hom_comp, h₂]
        refine Eq.trans ?_ (congrArg Prod.snd (subrepresentationLift_hom_apply _ _ _ _ _ _ t)).symm
        exact (congrArg Prod.snd (ContinuousLinearMap.prod_apply _ _ t)).symm))))

/-- **Banach representations have pullbacks**: the pullback of `f` and `g` is the closed invariant
subspace `{(x, y) | f x = g y}` of `X × Y`. -/
instance : HasPullbacks (BanachRep.{w} 𝕜 G) :=
  @hasPullbacks_of_hasLimit_cospan _ _ fun {_ _ _ f g} => HasLimit.mk ⟨_, pullbackConeIsLimit f g⟩

/-- **Surjections are stable under base change**: in a pullback square, the map opposite a
surjection is surjective. -/
private theorem surjective_of_isPullback {P : BanachRep.{w} 𝕜 G} {fst : P ⟶ X} {snd : P ⟶ Y}
    (h : IsPullback fst snd f g) (hg : Function.Surjective g.hom) :
    Function.Surjective fst.hom := by
  let h₀ : IsPullback (pullbackCone f g).fst (pullbackCone f g).snd f g :=
    IsPullback.of_isLimit (pullbackConeIsLimit f g)
  let e := h.isoIsPullback _ _ h₀
  have hfst : fst = e.hom ≫ (pullbackCone f g).fst := (h.isoIsPullback_hom_fst _ _ h₀).symm
  intro x
  obtain ⟨y, hy⟩ := hg (f.hom x)
  obtain ⟨q, hq⟩ := (bijective_of_isIso e.hom).2
    ⟨(x, y), (mem_pullbackSubmodule f g (x, y)).mpr hy.symm⟩
  refine ⟨q, ?_⟩
  rw [hfst, hom_comp, ContinuousLinearMap.comp_apply, hq]
  exact pullbackCone_fst_hom_apply f g _

end Pullback

/-! ### Pushouts of inflations -/

section Pushout

variable {A A' B : BanachRep.{w} 𝕜 G} (i : A ⟶ A') (f : A ⟶ B)
  (hi : Function.Injective i.hom) (hc : IsClosed (Set.range i.hom))

/-- The invariant subspace `{(f a, -i a)}` of `B × A'`. -/
private noncomputable def pushoutSubmodule : Submodule 𝕜 (B × A') :=
  LinearMap.range ((f.hom.prod (-i.hom) : A →L[𝕜] B × A') : A →ₗ[𝕜] B × A')

private theorem mem_pushoutSubmodule (x : prod B A') :
    x ∈ pushoutSubmodule i f ↔ ∃ a, f.hom a = x.1 ∧ -i.hom a = x.2 := by
  simp [pushoutSubmodule, Prod.ext_iff]

private theorem pushoutSubmodule_invariant :
    ∀ (t : G), ∀ x ∈ pushoutSubmodule i f, (prod B A').ρ t x ∈ pushoutSubmodule i f := by
  intro t x hx
  obtain ⟨a, ha₁, ha₂⟩ := (mem_pushoutSubmodule i f x).mp hx
  exact (mem_pushoutSubmodule i f _).mpr ⟨A.ρ t a, by simp [← ha₁, ← ha₂]⟩

include hi hc in
/-- The subspace `{(f a, -i a)}` is closed: the map `a ↦ (f a, -i a)` is antilipschitz because `i`
is, by the open mapping theorem. -/
private theorem isClosed_pushoutSubmodule :
    IsClosed (pushoutSubmodule i f : Set (prod B A')) := by
  obtain ⟨K, hK⟩ := i.hom.antilipschitz_of_injective_of_isClosed_range hi hc
  refine AntilipschitzWith.isClosed_range (K := K) ?_ (f.hom.prod (-i.hom)).uniformContinuous
  refine ContinuousLinearMap.antilipschitz_of_bound _ fun a => ?_
  calc ‖a‖ ≤ K * ‖i.hom a‖ := by simpa using hK.le_mul_dist a 0
    _ = K * ‖(f.hom.prod (-i.hom) a).2‖ := by simp
    _ ≤ K * ‖f.hom.prod (-i.hom) a‖ := by gcongr; exact norm_snd_le _

/-- The pushout object `(B × A') / {(f a, -i a)}`. -/
private noncomputable abbrev pushoutObj : BanachRep.{w} 𝕜 G :=
  quotient (prod B A') _ (pushoutSubmodule_invariant i f) (isClosed_pushoutSubmodule i f hi hc)

/-- The projection `B × A' ⟶ pushoutObj`. -/
private noncomputable abbrev pushoutπ : prod B A' ⟶ pushoutObj i f hi hc :=
  quotientπ _ _ _ _

/-- The pushout square of `f` along the inflation `i`: the maps `B ⟶ pushoutObj` and
`A' ⟶ pushoutObj` induced by the two inclusions into `B × A'`. -/
private noncomputable def pushoutCocone : PushoutCocone f i :=
  PushoutCocone.mk (W := pushoutObj i f hi hc) (prodInl B A' ≫ pushoutπ i f hi hc)
    (prodInr B A' ≫ pushoutπ i f hi hc)
    (hom_ext (ContinuousLinearMap.ext fun a => by
      simp only [hom_comp, ContinuousLinearMap.comp_apply]
      rw [prodInl_hom_apply, prodInr_hom_apply]
      exact (quotientπ_hom_apply_eq_iff _ _ _ _ _ _).mpr
        ((mem_pushoutSubmodule i f _).mpr ⟨a, by simp, by simp⟩)))

/-- A pair of maps out of `B` and `A'` agreeing on `A` gives a map out of `B × A'` killing
`{(f a, -i a)}`. -/
private theorem pushout_desc_aux (s : PushoutCocone f i) :
    ∀ x ∈ pushoutSubmodule i f, (prodFst B A' ≫ s.inl + prodSnd B A' ≫ s.inr).hom x = 0 := by
  intro x hx
  obtain ⟨a, ha₁, ha₂⟩ := (mem_pushoutSubmodule i f x).mp hx
  have h : s.inl.hom (f.hom a) = s.inr.hom (i.hom a) := by
    simpa using congr(($(s.condition)).hom a)
  rw [hom_add, _root_.add_apply, hom_comp, hom_comp, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.comp_apply, prodFst_hom_apply, prodSnd_hom_apply, ← ha₁, ← ha₂, map_neg, h,
    add_neg_cancel]

/-- The pushout cocone of `f` along the inflation `i` is a colimit. -/
private noncomputable def pushoutCoconeIsColimit : IsColimit (pushoutCocone i f hi hc) :=
  PushoutCocone.IsColimit.mk (pushoutCocone i f hi hc).condition
    (fun s => quotientDesc _ _ _ _ (prodFst B A' ≫ s.inl + prodSnd B A' ≫ s.inr)
      (pushout_desc_aux i f s))
    (fun s => by simp [pushoutCocone])
    (fun s => by simp [pushoutCocone])
    (fun s m h₁ h₂ => (cancel_epi (pushoutπ i f hi hc)).mp <| by
      -- The legs of `pushoutCocone` are `prodInl ≫ pushoutπ` and `prodInr ≫ pushoutπ`; its cone
      -- point is `pushoutObj` only by unfolding `PushoutCocone.mk`, which is why `h₁` and `h₂` are
      -- restated rather than rewritten with `PushoutCocone.mk_inl` and `PushoutCocone.mk_inr`.
      have h₁' : prodInl B A' ≫ pushoutπ i f hi hc ≫ m = s.inl :=
        (Category.assoc _ _ _).symm.trans h₁
      have h₂' : prodInr B A' ≫ pushoutπ i f hi hc ≫ m = s.inr :=
        (Category.assoc _ _ _).symm.trans h₂
      -- Both maps are determined by their restrictions to `B` and `A'`, through `B × A'`.
      calc pushoutπ i f hi hc ≫ m
          = (prodFst B A' ≫ prodInl B A' + prodSnd B A' ≫ prodInr B A') ≫
              pushoutπ i f hi hc ≫ m := by
            rw [prodFst_prodInl_add_prodSnd_prodInr, Category.id_comp]
        _ = prodFst B A' ≫ s.inl + prodSnd B A' ≫ s.inr := by
            simp only [Preadditive.add_comp, Category.assoc, h₁', h₂']
        _ = _ := (quotientπ_comp_quotientDesc _ _ _ _ _ _).symm)

/-- In the pushout, the map out of `B` is injective with closed range: its range is the kernel of
the induced map to the cokernel `A' / i(A)`. -/
private theorem pushoutCocone_inl_injective_isClosed_range :
    Function.Injective (pushoutCocone i f hi hc).inl.hom ∧
      IsClosed (Set.range (pushoutCocone i f hi hc).inl.hom) := by
  let R := LinearMap.range (i.hom : A →ₗ[𝕜] A')
  have hR : ∀ (t : G), ∀ a ∈ R, A'.ρ t a ∈ R := range_invariant i
  -- The map `ψ : pushoutObj ⟶ A' / i(A)` induced by `(b, a') ↦ [a']`.
  let ψ : pushoutObj i f hi hc ⟶ quotient A' R hR hc :=
    quotientDesc _ _ _ _ (prodSnd B A' ≫ quotientπ A' R hR hc) fun x hx => by
      obtain ⟨a, -, ha₂⟩ := (mem_pushoutSubmodule i f x).mp hx
      rw [hom_comp, ContinuousLinearMap.comp_apply, prodSnd_hom_apply]
      exact (quotientπ_hom_apply_eq_zero_iff _ _ _ _ _).mpr ⟨-a, by rw [map_neg]; exact ha₂⟩
  have hN := quotientπ_hom_apply_eq_iff (prod B A') (pushoutSubmodule i f)
    (pushoutSubmodule_invariant i f) (isClosed_pushoutSubmodule i f hi hc)
  have hinl : ∀ b, (pushoutCocone i f hi hc).inl.hom b = (pushoutπ i f hi hc).hom (b, 0) :=
    fun b => by
      -- The first leg of `pushoutCocone` is `prodInl ≫ pushoutπ`, by `PushoutCocone.mk`.
      change (prodInl B A' ≫ pushoutπ i f hi hc).hom b = _
      rw [hom_comp, ContinuousLinearMap.comp_apply, prodInl_hom_apply]
  refine ⟨fun b b' hbb' => ?_, ?_⟩
  · rw [hinl, hinl] at hbb'
    obtain ⟨a, ha₁, ha₂⟩ := (mem_pushoutSubmodule i f _).mp ((hN (b, 0) (b', 0)).mp hbb')
    have ha : a = 0 := hi (by simpa using ha₂)
    simpa [ha, sub_eq_zero] using ha₁.symm
  · have hrange : Set.range (pushoutCocone i f hi hc).inl.hom = ψ.hom ⁻¹' {0} := by
      ext q
      obtain ⟨⟨b, a'⟩, rfl⟩ := quotientπ_surjective (prod B A') (pushoutSubmodule i f) _
        (isClosed_pushoutSubmodule i f hi hc) q
      have hψ : ψ.hom ((pushoutπ i f hi hc).hom (b, a')) = (quotientπ A' R hR hc).hom a' := by
        dsimp only [ψ]
        rw [quotientDesc_hom_quotientπ_hom, hom_comp, ContinuousLinearMap.comp_apply,
          prodSnd_hom_apply]
      have key : ψ.hom ((pushoutπ i f hi hc).hom (b, a')) = 0 ↔ a' ∈ R := by
        rw [hψ]
        exact quotientπ_hom_apply_eq_zero_iff A' R hR hc a'
      refine ⟨fun ⟨b', hb'⟩ => key.mpr ?_, fun hq => ?_⟩
      · rw [hinl] at hb'
        obtain ⟨a, -, ha₂⟩ := (mem_pushoutSubmodule i f _).mp ((hN (b', 0) (b, a')).mp hb')
        exact ⟨a, by simpa using ha₂⟩
      · obtain ⟨a, rfl⟩ := key.mp hq
        refine ⟨b + f.hom a, ?_⟩
        rw [hinl]
        exact (hN _ _).mpr ((mem_pushoutSubmodule i f _).mpr ⟨a, by simp, by simp⟩)
    rw [hrange]
    exact isClosed_singleton.preimage ψ.hom.continuous

end Pushout

/-! ### The exact structure -/

/-- **The strict exact structure on Banach representations**: the conflations are the
algebraically exact sequences `0 → X₁ → X₂ → X₃ → 0`. -/
noncomputable def exactStructure : ExactStructure (BanachRep.{w} 𝕜 G) where
  toConflationClass := conflationClass
  isInflation_id X := (conflationClass_isInflation_iff _).mpr
    ⟨Function.injective_id, by simp⟩
  isDeflation_id X := (conflationClass_isDeflation_iff _).mpr Function.surjective_id
  isInflation_comp i j hi hj := by
    rw [conflationClass_isInflation_iff] at hi hj ⊢
    have hij : Function.Injective (i ≫ j).hom := hj.1.comp hi.1
    refine ⟨hij, ?_⟩
    obtain ⟨K, hK⟩ := i.hom.antilipschitz_of_injective_of_isClosed_range hi.1 hi.2
    obtain ⟨L, hL⟩ := j.hom.antilipschitz_of_injective_of_isClosed_range hj.1 hj.2
    exact (hL.comp hK).isClosed_range (i ≫ j).hom.uniformContinuous
  isDeflation_comp p q hp hq := by
    rw [conflationClass_isDeflation_iff] at hp hq ⊢
    exact hq.comp hp
  hasPushouts_inflations := ⟨fun {_ _ _ i} f hi => by
    obtain ⟨hi, hc⟩ := (conflationClass_isInflation_iff i).mp hi
    have : HasPushout f i := HasColimit.mk ⟨_, pushoutCoconeIsColimit i f hi hc⟩
    exact hasPushout_symmetry f i⟩
  isStableUnderCobaseChange_inflations := ⟨fun {_ _ _ _ i f f' g'} sq hi => by
    obtain ⟨hi, hc⟩ := (conflationClass_isInflation_iff i).mp hi
    let h₀ : IsPushout f i (pushoutCocone i f hi hc).inl (pushoutCocone i f hi hc).inr :=
      IsPushout.of_isColimit (pushoutCoconeIsColimit i f hi hc)
    have h := MorphismProperty.RespectsIso.postcomp conflationClass.inflations
      (h₀.isoIsPushout _ _ sq).hom _ ((conflationClass_isInflation_iff _).mpr
        (pushoutCocone_inl_injective_isClosed_range i f hi hc))
    rwa [h₀.inl_isoIsPushout_hom] at h⟩
  hasPullbacks_deflations := inferInstance
  isStableUnderBaseChange_deflations := ⟨fun {_ _ _ _ f g _ _} sq hg =>
    (conflationClass_isDeflation_iff _).mpr
      (surjective_of_isPullback f g sq.flip ((conflationClass_isDeflation_iff g).mp hg))⟩

/-- **The conflations are the algebraically exact sequences.** -/
theorem exactStructure_conflation_iff (S : ShortComplex (BanachRep.{w} 𝕜 G)) :
    exactStructure.Conflation S ↔ Function.Injective S.f.hom ∧ Function.Surjective S.g.hom ∧
      Function.Exact S.f.hom S.g.hom :=
  Iff.rfl

/-- **The inflations are the injective morphisms with closed range.** -/
theorem exactStructure_isInflation_iff (i : X ⟶ Y) :
    exactStructure.IsInflation i ↔ Function.Injective i.hom ∧ IsClosed (Set.range i.hom) :=
  conflationClass_isInflation_iff i

/-- **The deflations are the surjective morphisms.** -/
theorem exactStructure_isDeflation_iff (p : X ⟶ Y) :
    exactStructure.IsDeflation p ↔ Function.Surjective p.hom :=
  conflationClass_isDeflation_iff p

/-- **Inflations are strict**: an inflation is a homeomorphism onto its closed range. -/
theorem isClosedEmbedding_of_isInflation {i : X ⟶ Y} (hi : exactStructure.IsInflation i) :
    IsClosedEmbedding i.hom := by
  obtain ⟨hi, hc⟩ := (exactStructure_isInflation_iff i).mp hi
  obtain ⟨K, hK⟩ := i.hom.antilipschitz_of_injective_of_isClosed_range hi hc
  exact hK.isClosedEmbedding i.hom.uniformContinuous

/-- **Deflations are strict**: by the open mapping theorem, a deflation is an open quotient map. -/
theorem isOpenQuotientMap_of_isDeflation {p : X ⟶ Y} (hp : exactStructure.IsDeflation p) :
    IsOpenQuotientMap p.hom :=
  have hp := (exactStructure_isDeflation_iff p).mp hp
  ⟨hp, p.hom.continuous, p.hom.isOpenMap hp⟩

end BanachRep

end TauCeti
