/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Abelian.Exact
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic
public import TauCeti.CategoryTheory.Abelian.RightDerived
public import TauCeti.CategoryTheory.Sites.SheafCohomology.Pullback
public import TauCeti.CategoryTheory.Sites.SheafCohomology.HigherDirectImage
public import TauCeti.CategoryTheory.Sites.SheafCohomology.LongExactSequence

/-!
# The edge map of the Leray spectral sequence

Let `pb : Sheaf J Ab ⥤ Sheaf K Ab` be an exact additive functor between categories of abelian
sheaves on sites `(C, J)` and `(D, K)` with a right adjoint `pf`, and let `c : ℤ_K ⟶ pb ℤ_J` be a
map between the constant sheaves `ℤ`. For a morphism of sites, `pb` is the inverse image `f⁻¹`,
`pf` is the pushforward `f_*` and `c` is the canonical comparison of constant sheaves.

For an abelian sheaf `F` on `(D, K)`, the edge map `E₂^{n,0} = Hⁿ(C, f_* F) ⟶ Hⁿ(D, F)` of the
Leray spectral sequence is the pullback `Sheaf.H.pullback pb c` of cohomology to
`Hⁿ(D, f⁻¹ f_* F)` followed by the map induced by the counit `f⁻¹ f_* F ⟶ F`
(Stacks, Lemma 21.14.5 (0732) and Remark 21.14.4 (08J6)). This file defines it
(`Sheaf.H.lerayEdge`) and proves that it is natural in `F`, compatible with the connecting
homomorphisms of short exact sequences that stay exact after pushforward, and in degree zero
given by the adjunction, hence bijective when `c` is an isomorphism, and injective in degree one,
the first map of the five-term exact sequence; it is the identity for the identity morphism and
compatible with composition of morphisms. By dimension shifting along the injective
embeddings of `F`, if the higher direct images `Rᵠ f_* F` vanish for `0 < q < n`, the edge map is
injective in degree `n`, and bijective if moreover `Rⁿ f_* F = 0`: in the Leray spectral sequence
no differential reaches `E₂^{n,0}`. When all higher direct images of `F` vanish, for instance when
`f_*` is exact, it is bijective in every degree: this is Leray's acyclicity theorem, also stated
for a morphism of sites (`Sheaf.H.lerayEdge_sheafAdjunctionContinuous_bijective`).

## Main declarations

* `CategoryTheory.Sheaf.H.lerayEdge`: the edge map `Hⁿ(C, f_* F) →+ Hⁿ(D, F)`.
* `CategoryTheory.Sheaf.H.lerayEdge_naturality`: naturality in `F`.
* `CategoryTheory.Sheaf.H.lerayEdge_δ`: compatibility with connecting homomorphisms.
* `CategoryTheory.Sheaf.H.lerayEdge_id`, `CategoryTheory.Sheaf.H.lerayEdge_comp_apply`: the edge
  map of the identity is the identity, and edge maps compose along composite morphisms.
* `CategoryTheory.Sheaf.H.addEquiv₀_lerayEdge`, `CategoryTheory.Sheaf.H.lerayEdge_zero_bijective`:
  the edge map in degree zero.
* `CategoryTheory.Sheaf.H.lerayEdge_one_injective`: the edge map is injective in degree one.
* `CategoryTheory.Sheaf.H.lerayEdge_succ_injective`,
  `CategoryTheory.Sheaf.H.lerayEdge_succ_surjective`: dimension shifting for the edge map.
* `CategoryTheory.Sheaf.H.lerayEdge_injective_of_isZero_rightDerived`,
  `CategoryTheory.Sheaf.H.lerayEdge_bijective_of_isZero_rightDerived`: the edge map in degree `n`
  when the higher direct images vanish below degree `n`, respectively up to degree `n`.
* `CategoryTheory.Sheaf.H.lerayEdge_bijective`: the edge map is bijective in every degree when
  `f_*` is exact.
* `CategoryTheory.Sheaf.H.lerayEdge_sheafAdjunctionContinuous_bijective`: Leray's acyclicity
  theorem for a morphism of sites.

## References

* [Stacks Project, Section 21.14 (Tag 072X)](https://stacks.math.columbia.edu/tag/072X),
  Lemmas 21.14.1 (072Z), 21.14.5 (0732), 21.14.6 (0733) and Remark 21.14.4 (08J6).
-/

public section

open CategoryTheory Abelian Limits AddCommGrpCat

universe w w₁ w₂ w₃

namespace CategoryTheory.Sheaf.H

variable {C : Type*} [Category* C] {J : GrothendieckTopology C}
  {D : Type*} [Category* D] {K : GrothendieckTopology D}
  [HasSheafify J AddCommGrpCat.{w}] [HasSheafify K AddCommGrpCat.{w}]
  [HasExt.{w₁} (Sheaf J AddCommGrpCat.{w})] [HasExt.{w₂} (Sheaf K AddCommGrpCat.{w})]
  {pb : Sheaf J AddCommGrpCat.{w} ⥤ Sheaf K AddCommGrpCat.{w}} [pb.Additive]
  [PreservesFiniteLimits pb] [PreservesFiniteColimits pb]
  {pf : Sheaf K AddCommGrpCat.{w} ⥤ Sheaf J AddCommGrpCat.{w}} (adj : pb ⊣ pf)
  (c : (constantSheaf K AddCommGrpCat.{w}).obj (of (ULift ℤ)) ⟶
    pb.obj ((constantSheaf J AddCommGrpCat.{w}).obj (of (ULift ℤ))))

noncomputable section

/-- The edge map `Hⁿ(C, f_* F) →+ Hⁿ(D, F)` of the Leray spectral sequence, for an exact functor
`pb` with right adjoint `pf` and a comparison `c : ℤ_K ⟶ pb ℤ_J` of constant sheaves: the
pullback of cohomology to `Hⁿ(D, pb (pf F))` followed by the map induced by the counit
`pb (pf F) ⟶ F`. -/
def lerayEdge (F : Sheaf K AddCommGrpCat.{w}) (n : ℕ) : H (pf.obj F) n →+ H F n :=
  (H.map (adj.counit.app F) n).comp (pullback pb c (pf.obj F) n)

lemma lerayEdge_apply {F : Sheaf K AddCommGrpCat.{w}} {n : ℕ} (x : H (pf.obj F) n) :
    lerayEdge adj c F n x = H.map (adj.counit.app F) n (pullback pb c (pf.obj F) n x) := (rfl)

/-- The edge map is natural in the coefficient sheaf. -/
lemma lerayEdge_naturality {F₁ F₂ : Sheaf K AddCommGrpCat.{w}} (φ : F₁ ⟶ F₂) {n : ℕ}
    (x : H (pf.obj F₁) n) :
    lerayEdge adj c F₂ n (H.map (pf.map φ) n x) = H.map φ n (lerayEdge adj c F₁ n x) := by
  rw [lerayEdge_apply, lerayEdge_apply, pullback_naturality, ← H.map_comp_apply,
    ← H.map_comp_apply, adj.counit_naturality φ]

/-- The edge map commutes with the connecting homomorphisms of a short exact sequence `S` of
abelian sheaves on `(D, K)` whose pushforward `pf S` is short exact. -/
lemma lerayEdge_δ [pf.PreservesZeroMorphisms] {S : ShortComplex (Sheaf K AddCommGrpCat.{w})}
    (hS : S.ShortExact) (hS' : (S.map pf).ShortExact) (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁)
    (x : H (pf.obj S.X₃) n₀) :
    lerayEdge adj c S.X₁ n₁ (H.δ hS' n₀ n₁ h x) =
      H.δ hS n₀ n₁ h (lerayEdge adj c S.X₃ n₀ x) := by
  let φ : (S.map pf).map pb ⟶ S :=
    { τ₁ := adj.counit.app S.X₁
      τ₂ := adj.counit.app S.X₂
      τ₃ := adj.counit.app S.X₃ }
  exact (congrArg (H.map (adj.counit.app S.X₁) n₁) (pullback_δ pb c hS' n₀ n₁ h x)).trans
    (H.δ_naturality n₀ n₁ h (hS'.map_of_exact pb) hS φ _).symm

/-- The edge map of the identity, with the identity comparison of constant sheaves, is the
identity: for the identity morphism of sites the Leray spectral sequence degenerates. -/
@[simp]
lemma lerayEdge_id (F : Sheaf K AddCommGrpCat.{w}) (n : ℕ) :
    lerayEdge Adjunction.id (𝟙 _) F n = AddMonoidHom.id _ := by
  ext x
  rw [lerayEdge_apply, pullback_id_apply]
  exact H.map_id_apply x

/-- The edge maps of two composable morphisms compose to the edge map of the composite: for
`f : D ⟶ C` and `g : E ⟶ D`, the edge map `Hⁿ(C, f_* g_* F) ⟶ Hⁿ(E, F)` of `f ∘ g` is the edge
map of `f` for `g_* F` followed by the edge map of `g`, for the composite comparison
`ℤ ⟶ g⁻¹ ℤ ⟶ g⁻¹ f⁻¹ ℤ` of constant sheaves. -/
lemma lerayEdge_comp_apply {E : Type*} [Category* E] {L : GrothendieckTopology E}
    [HasSheafify L AddCommGrpCat.{w}] [HasExt.{w₃} (Sheaf L AddCommGrpCat.{w})]
    {pb₂ : Sheaf K AddCommGrpCat.{w} ⥤ Sheaf L AddCommGrpCat.{w}} [pb₂.Additive]
    [PreservesFiniteLimits pb₂] [PreservesFiniteColimits pb₂]
    {pf₂ : Sheaf L AddCommGrpCat.{w} ⥤ Sheaf K AddCommGrpCat.{w}} (adj₂ : pb₂ ⊣ pf₂)
    (c₂ : (constantSheaf L AddCommGrpCat.{w}).obj (of (ULift ℤ)) ⟶
      pb₂.obj ((constantSheaf K AddCommGrpCat.{w}).obj (of (ULift ℤ))))
    (F : Sheaf L AddCommGrpCat.{w}) (n : ℕ) (x : H (pf.obj (pf₂.obj F)) n) :
    lerayEdge (adj.comp adj₂) (c₂ ≫ pb₂.map c) F n x =
      lerayEdge adj₂ c₂ F n (lerayEdge adj c (pf₂.obj F) n x) := by
  rw [lerayEdge_apply, lerayEdge_apply, lerayEdge_apply, pullback_comp_apply,
    pullback_naturality, ← H.map_comp_apply, Adjunction.comp_counit_app]
  simp only [Functor.comp_obj]

/-- In degree zero, the edge map sends the class of a map `g : ℤ_J ⟶ f_* F` to its adjoint
`ℤ_K ⟶ pb ℤ_J ⟶ F`, precomposed with `c`. -/
@[simp]
lemma addEquiv₀_lerayEdge {F : Sheaf K AddCommGrpCat.{w}} (x : H (pf.obj F) 0) :
    Ext.addEquiv₀ (lerayEdge adj c F 0 x) = c ≫ (adj.homEquiv _ _).symm (Ext.addEquiv₀ x) := by
  simp [lerayEdge_apply, H.addEquiv₀_map, Adjunction.homEquiv_counit]

/-- When the comparison `c` of constant sheaves is an isomorphism, as it is for a morphism of
sites, the edge map is bijective in degree zero: both sides are the global sections of `F`. -/
lemma lerayEdge_zero_bijective [IsIso c] (F : Sheaf K AddCommGrpCat.{w}) :
    Function.Bijective (lerayEdge adj c F 0) := by
  rw [← (Ext.addEquiv₀ (X := (constantSheaf K AddCommGrpCat.{w}).obj (of (ULift ℤ)))
    (Y := F)).bijective.of_comp_iff']
  have h : ⇑Ext.addEquiv₀ ∘ ⇑(lerayEdge adj c F 0) =
      (c ≫ ·) ∘ (adj.homEquiv _ _).symm ∘ Ext.addEquiv₀ :=
    funext (addEquiv₀_lerayEdge adj c)
  refine h ▸ Function.Bijective.comp ⟨fun g g' hg ↦ ?_, fun g ↦ ⟨inv c ≫ g, by simp⟩⟩
    ((adj.homEquiv _ _).symm.bijective.comp Ext.addEquiv₀.bijective)
  simpa using congrArg (inv c ≫ ·) hg

end

/-- When the comparison `c` of constant sheaves is an isomorphism, the edge map is injective in
degree one: `H¹(C, f_* F) ⟶ H¹(D, F)` is the first map of the five-term exact sequence of the
Leray spectral sequence (Stacks, Lemma 21.14.5 (0732)). -/
lemma lerayEdge_one_injective [IsIso c] [EnoughInjectives (Sheaf K AddCommGrpCat.{w})]
    (F : Sheaf K AddCommGrpCat.{w}) : Function.Injective (lerayEdge adj c F 1) := by
  -- Embed `F` into an injective sheaf `I`. As `H¹(C, f_* I) = 0`, a class of `H¹(C, f_* F)` is
  -- the connecting image of a section `y` of the cokernel `Q` of `f_* F ⟶ f_* I`. If its edge
  -- image vanishes, the adjoint of `y` lifts along `I ⟶ I / F`, so `y` lifts to `f_* I`, because
  -- `Q` embeds into `f_* (I / F)`; hence the class is zero.
  have := adj.rightAdjoint_preservesLimits
  have := adj.right_adjoint_additive
  let ι := Injective.ι F
  have hS : (ShortComplex.mk ι (cokernel.π ι) (cokernel.condition ι)).ShortExact :=
    { exact := ShortComplex.exact_cokernel ι }
  have hT : (ShortComplex.mk (pf.map ι) (cokernel.π (pf.map ι))
      (cokernel.condition (pf.map ι))).ShortExact :=
    { exact := ShortComplex.exact_cokernel (pf.map ι) }
  -- The comparison `Q ⟶ f_* (I / F)` is a monomorphism, as `f_*` is left exact.
  let g₃ : cokernel (pf.map ι) ⟶ pf.obj (cokernel ι) :=
    cokernel.desc (pf.map ι) (pf.map (cokernel.π ι)) (by
      rw [← pf.map_comp, cokernel.condition, pf.map_zero])
  have : Mono g₃ :=
    (hS.exact.map_of_mono_of_preservesKernel pf hS.mono_f inferInstance).mono_cokernelDesc
  let φ : (ShortComplex.mk (pf.map ι) (cokernel.π (pf.map ι)) (cokernel.condition _)).map pb ⟶
      ShortComplex.mk ι (cokernel.π ι) (cokernel.condition ι) :=
    { τ₁ := adj.counit.app F
      τ₂ := adj.counit.app (Injective.under F)
      τ₃ := pb.map g₃ ≫ adj.counit.app (cokernel ι)
      comm₁₂ := (adj.counit.naturality ι).symm
      comm₂₃ := by
        dsimp only [ShortComplex.map_g]
        rw [← pb.map_comp_assoc, cokernel.π_desc]
        exact (adj.counit.naturality (cokernel.π ι)).symm }
  refine (injective_iff_map_eq_zero _).2 fun x hx ↦ ?_
  -- `f_* I` is injective (Stacks, Lemma 21.14.1 (072Z)), so `H¹(C, f_* I) = 0`.
  have := Injective.injective_of_adjoint adj (Injective.under F)
  obtain ⟨y, hy⟩ := (exact_δ_map hT 0 1 rfl x).1 (Subsingleton.elim _ _)
  have hx' : H.δ hS 0 1 rfl (H.map φ.τ₃ 0 (pullback pb c _ 0 y)) = 0 :=
    (H.δ_naturality 0 1 rfl (hT.map_of_exact pb) hS φ _).trans
      ((congrArg (H.map φ.τ₁ 1) (pullback_δ pb c hT 0 1 rfl y)).symm.trans
        ((congrArg (lerayEdge adj c F 1) hy).trans hx))
  obtain ⟨z, hz⟩ := (exact_map_δ hS 0 1 rfl _).1 hx'
  have hz' := congrArg Ext.addEquiv₀ hz
  rw [H.addEquiv₀_map, H.addEquiv₀_map, addEquiv₀_pullback] at hz'
  -- The adjoint of the lift of `y` to `I / F`.
  let a : _ ⟶ pf.obj (Injective.under F) := (adj.homEquiv _ _) (inv c ≫ Ext.addEquiv₀ z)
  have ha : a ≫ cokernel.π (pf.map ι) = Ext.addEquiv₀ y := by
    rw [← cancel_mono g₃, Category.assoc, cokernel.π_desc, ← adj.homEquiv_naturality_right,
      Category.assoc, hz', Category.assoc, IsIso.inv_hom_id_assoc]
    dsimp only [φ]
    rw [← pb.map_comp_assoc, ← Adjunction.homEquiv_counit, Equiv.apply_symm_apply]
  obtain rfl : y = H.map (cokernel.π (pf.map ι)) 0 (Ext.addEquiv₀.symm a) :=
    Ext.addEquiv₀.injective (by rw [H.addEquiv₀_map, AddEquiv.apply_symm_apply, ha])
  rw [← hy]
  exact (exact_map_δ hT 0 1 rfl).apply_apply_eq_zero _

/-- Dimension shifting for the edge map, surjectivity: for a short exact sequence
`0 ⟶ F ⟶ I ⟶ Q ⟶ 0` with `I` injective whose pushforward is short exact, if the edge map of `Q`
is surjective in degree `n`, that of `F` is surjective in degree `n + 1`, as `Hⁿ⁺¹(I) = 0`. -/
lemma lerayEdge_succ_surjective [pf.PreservesZeroMorphisms]
    {S : ShortComplex (Sheaf K AddCommGrpCat.{w})} (hS : S.ShortExact) (hT : (S.map pf).ShortExact)
    [Injective S.X₂] {n : ℕ} (hQ : Function.Surjective (lerayEdge adj c S.X₃ n)) :
    Function.Surjective (lerayEdge adj c S.X₁ (n + 1)) := by
  intro x
  obtain ⟨y, rfl⟩ := (exact_δ_map hS n (n + 1) rfl x).1 (Subsingleton.elim _ _)
  obtain ⟨y, rfl⟩ := hQ y
  exact ⟨H.δ hT n (n + 1) rfl y, lerayEdge_δ adj c hS hT n (n + 1) rfl y⟩

/-- Dimension shifting for the edge map, injectivity: for a short exact sequence
`0 ⟶ F ⟶ I ⟶ Q ⟶ 0` with `I` injective whose pushforward is short exact, if the edge map of `I`
is surjective and that of `Q` injective in degree `n`, the edge map of `F` is injective in degree
`n + 1`, as `Hⁿ⁺¹(C, f_* I) = 0`. -/
lemma lerayEdge_succ_injective [pf.PreservesZeroMorphisms]
    {S : ShortComplex (Sheaf K AddCommGrpCat.{w})} (hS : S.ShortExact) (hT : (S.map pf).ShortExact)
    [Injective S.X₂] {n : ℕ} (hI : Function.Surjective (lerayEdge adj c S.X₂ n))
    (hQ : Function.Injective (lerayEdge adj c S.X₃ n)) :
    Function.Injective (lerayEdge adj c S.X₁ (n + 1)) := by
  -- `f_* I` is injective (Stacks, Lemma 21.14.1 (072Z)), so `Hⁿ⁺¹(C, f_* I) = 0`.
  have := Injective.injective_of_adjoint adj S.X₂
  refine (injective_iff_map_eq_zero _).2 fun x hx ↦ ?_
  obtain ⟨y, rfl⟩ := (exact_δ_map hT n (n + 1) rfl x).1
    (Subsingleton.elim (α := H (pf.obj S.X₂) (n + 1)) _ _)
  rw [lerayEdge_δ adj c hS hT] at hx
  obtain ⟨z, hz⟩ := (exact_map_δ hS n (n + 1) rfl _).1 hx
  obtain ⟨z, rfl⟩ := hI z
  obtain rfl : H.map (pf.map S.g) n z = y := hQ ((lerayEdge_naturality adj c _ z).trans hz)
  exact (exact_map_δ hT n (n + 1) rfl).apply_apply_eq_zero z

/-- When the comparison `c` of constant sheaves is an isomorphism and the higher direct images of
`F` vanish in degrees `1, …, n`, the edge map `Hⁿ(C, f_* F) ⟶ Hⁿ(D, F)` is bijective
(Stacks, Lemma 21.14.6 (0733) when all of them vanish). -/
lemma lerayEdge_bijective_of_isZero_rightDerived [IsIso c]
    [EnoughInjectives (Sheaf K AddCommGrpCat.{w})] [pf.Additive] {F : Sheaf K AddCommGrpCat.{w}}
    {n : ℕ} (hF : ∀ q < n, IsZero ((pf.rightDerived (q + 1)).obj F)) :
    Function.Bijective (lerayEdge adj c F n) := by
  have := adj.rightAdjoint_preservesLimits
  induction n generalizing F with
  | zero => exact lerayEdge_zero_bijective adj c F
  | succ n ih =>
    -- Embed `F` into an injective sheaf `I` with cokernel `Q`. As `R¹ f_* F = 0`, the pushforward
    -- of `0 ⟶ F ⟶ I ⟶ Q ⟶ 0` is short exact, and the higher direct images of `Q` vanish in
    -- degrees `1, …, n`, so the edge maps of `I` and `Q` in degree `n` are bijective.
    let S := (EnoughInjectives.presentation F).some.shortComplex
    have hS : S.ShortExact := InjectivePresentation.shortExact_shortComplex _
    have hT := pf.shortExact_map_of_isZero_rightDerived_one hS (hF 0 n.succ_pos)
    have hQ := ih fun q hq ↦ pf.isZero_rightDerived_obj_X₃_of_isZero hS q (hF (q + 1) (by lia))
    have hI := ih fun q _ ↦ pf.isZero_rightDerived_obj_injective_succ q S.X₂
    exact ⟨lerayEdge_succ_injective adj c hS hT hI.2 hQ.1,
      lerayEdge_succ_surjective adj c hS hT hQ.2⟩

/-- When the comparison `c` of constant sheaves is an isomorphism and the higher direct images of
`F` vanish in degrees `1, …, n - 1`, the edge map `Hⁿ(C, f_* F) ⟶ Hⁿ(D, F)` is injective: in the
Leray spectral sequence, no differential reaches `E₂^{n,0}`. -/
lemma lerayEdge_injective_of_isZero_rightDerived [IsIso c]
    [EnoughInjectives (Sheaf K AddCommGrpCat.{w})] [pf.Additive] {F : Sheaf K AddCommGrpCat.{w}}
    {n : ℕ} (hF : ∀ q, q + 1 < n → IsZero ((pf.rightDerived (q + 1)).obj F)) :
    Function.Injective (lerayEdge adj c F n) := by
  induction n generalizing F with
  | zero => exact (lerayEdge_zero_bijective adj c F).1
  | succ n ih =>
    rcases n with _ | n
    · exact lerayEdge_one_injective adj c F
    -- Dimension shifting along an injective embedding, as in
    -- `lerayEdge_bijective_of_isZero_rightDerived`.
    have := adj.rightAdjoint_preservesLimits
    let S := (EnoughInjectives.presentation F).some.shortComplex
    have hS : S.ShortExact := InjectivePresentation.shortExact_shortComplex _
    exact lerayEdge_succ_injective adj c hS
      (pf.shortExact_map_of_isZero_rightDerived_one hS (hF 0 (by lia)))
      (lerayEdge_bijective_of_isZero_rightDerived adj c
        fun q _ ↦ pf.isZero_rightDerived_obj_injective_succ q S.X₂).2
      (ih fun q hq ↦ pf.isZero_rightDerived_obj_X₃_of_isZero hS q (hF (q + 1) (by lia)))

/-- When the comparison `c` of constant sheaves is an isomorphism and the pushforward `pf` is
exact, so that all higher direct images vanish, the edge map `Hⁿ(C, f_* F) ⟶ Hⁿ(D, F)` is
bijective in every degree. -/
lemma lerayEdge_bijective [IsIso c] [EnoughInjectives (Sheaf K AddCommGrpCat.{w})]
    [pf.PreservesEpimorphisms] (F : Sheaf K AddCommGrpCat.{w}) (n : ℕ) :
    Function.Bijective (lerayEdge adj c F n) := by
  have := adj.rightAdjoint_preservesLimits
  have := adj.right_adjoint_additive
  have := Functor.preservesHomology_of_preservesEpis_and_kernels pf
  exact lerayEdge_bijective_of_isZero_rightDerived adj c fun q _ ↦ pf.isZero_rightDerived_succ F q

end CategoryTheory.Sheaf.H

namespace CategoryTheory.Sheaf.H

variable {C : Type*} [Category* C] {J : GrothendieckTopology C}
  {D : Type*} [Category* D] {K : GrothendieckTopology D}
  [HasSheafify J AddCommGrpCat.{w}] [HasSheafify K AddCommGrpCat.{w}]
  [HasExt.{w₁} (Sheaf J AddCommGrpCat.{w})] [HasExt.{w₂} (Sheaf K AddCommGrpCat.{w})]
  (u : C ⥤ D) [u.IsContinuous J K]
  [(u.sheafPushforwardContinuous AddCommGrpCat.{w} J K).IsRightAdjoint] [u.Final]
  [PreservesFiniteLimits (u.sheafPullback AddCommGrpCat.{w} J K)]

local instance : (u.sheafPullback AddCommGrpCat.{w} J K).Additive :=
  Functor.additive_of_preserves_binary_products _

local instance : PreservesFiniteColimits (u.sheafPullback AddCommGrpCat.{w} J K) :=
  letI := (u.sheafAdjunctionContinuous AddCommGrpCat.{w} J K).leftAdjoint_preservesColimits.{0, 0}
  inferInstance

/-- **Leray acyclicity for a morphism of sites.** For a morphism of sites given by `u : C ⥤ D`,
with pushforward `f_* = u.sheafPushforwardContinuous` and exact inverse image
`f⁻¹ = u.sheafPullback`, if an abelian sheaf `F` on `D` has no higher direct images
(`Rᵠ f_* F = 0` for `q > 0`, with `Rᵠ f_* = u.sheafHigherDirectImage AddCommGrpCat J K q`), then
the edge map `Hⁿ(C, f_* F) ⟶ Hⁿ(D, F)` is bijective in every degree
(Stacks, Lemma 21.14.6 (0733)). -/
theorem lerayEdge_sheafAdjunctionContinuous_bijective
    [EnoughInjectives (Sheaf K AddCommGrpCat.{w})] {F : Sheaf K AddCommGrpCat.{w}}
    (hF : ∀ q, IsZero ((u.sheafHigherDirectImage AddCommGrpCat.{w} J K (q + 1)).obj F))
    (n : ℕ) :
    Function.Bijective (lerayEdge (u.sheafAdjunctionContinuous AddCommGrpCat.{w} J K)
      (u.sheafPullbackConstantSheafIso AddCommGrpCat.{w} J K (of (ULift ℤ))).inv F n) :=
  lerayEdge_bijective_of_isZero_rightDerived _ _ fun q _ ↦ hF q

end CategoryTheory.Sheaf.H
