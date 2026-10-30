/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Sheaves.Cech
public import TauCeti.CategoryTheory.Sites.SheafCohomology.Cech.Exact
import Mathlib.Algebra.Category.Grp.Zero
import Mathlib.CategoryTheory.Sites.EpiMono
import TauCeti.Algebra.Category.Grp.IsSheafFor
import TauCeti.CategoryTheory.Sites.IsSheafFor
import TauCeti.CategoryTheory.Sites.SheafCohomology.LongExactSequence
import TauCeti.Topology.Sheaves.Flasque.Basic
import TauCeti.CategoryTheory.Limits.Lattice

/-!
# Cartan's criterion: Čech acyclicity on a basis implies cohomological acyclicity

Let `X` be a topological space and `B` a set of opens of `X` which is closed under binary
intersections, consists of quasi-compact opens, and is a basis of the topology inside each of its
members. Let `F` be a sheaf of abelian groups on `X` which is Čech acyclic for the finite covers of
members of `B` by members of `B`: for every finite nonempty family `U i` in `B` and every `Y ∈ B`
contained in their union, the augmented Čech complex of `V ↦ F(Y ∩ V)` for `U`, that is, of the
cover of `Y` by the opens `Y ∩ U i`, is exact (`TauCeti.Topology.IsCechAcyclicOn`). Then `F` has
no cohomology in positive degrees on the members of `B`
(`TauCeti.Topology.subsingleton_H'_succ_of_isCechAcyclicOn`).

This is how the vanishing of the higher cohomology of a quasi-coherent sheaf on an affine scheme is
deduced from the exactness of the Čech complexes of standard covers, with `B` the basic opens.

The proof is by dimension shifting along the chosen embedding `0 ⟶ F ⟶ I ⟶ Q ⟶ 0` of `F` into an
injective sheaf, which is flasque, so that its Čech complexes are exact for all finite covers
(`TopCat.Sheaf.quasiIso_cechAugmentation_prod_of_isFlasque`).

* On every `Y ∈ B`, the map `I(Y) ⟶ Q(Y)` is onto. A section `s` of `Q` over `Y` lifts locally,
  hence, `Y` being quasi-compact, on a finite cover of `Y` by members of `B`. The image presheaf
  `G` of `I ⟶ Q` sits in a sequence `0 ⟶ F ⟶ I ⟶ G ⟶ 0` of presheaves which is exact on every
  open, so the Čech complexes of the cover form a short exact sequence, and `G` is Čech acyclic
  for the cover because `F` and `I` are (`quasiIso_cechAugmentation_X₃_of_shortExact`). In degree
  `0` this is the sheaf condition for `G`, so the local lifts of `s` glue to a section of `G`
  over `Y`, which comes from `I(Y)` and maps to `s`.
* Hence `H¹(Y, F) = 0` for `Y ∈ B`, and the sequence `0 ⟶ F ⟶ I ⟶ Q ⟶ 0` is exact on the
  members of `B`, which are closed under finite intersections. Its Čech complexes for covers by
  members of `B` are then short exact, so `Q` is Čech acyclic on `B` as well.
* Finally `Hⁿ⁺²(Y, F) ≅ Hⁿ⁺¹(Y, Q)`, and induction on the degree, for all sheaves at once,
  concludes.

## Main definitions

* `TauCeti.Topology.IsCechAcyclicOn B F`: `F` is Čech acyclic for the finite covers of members of
  `B` by members of `B`.

## Main results

* `TauCeti.Topology.subsingleton_H'_succ_of_isCechAcyclicOn`: Cartan's criterion, `Hⁿ⁺¹(Y, F) = 0`
  for every member `Y` of `B`.
* `TauCeti.Topology.prod_pi_mem_of_inf_mem`: a set of opens closed under binary intersections
  contains the finite intersections `Y ∩ U (a 0) ∩ ⋯ ∩ U (a n)` of its members.
* `TopCat.Sheaf.exists_mem_lift_of_epi`: along an epimorphism of sheaves, sections lift locally on
  the members of a set of opens which contains a basis inside each of its members.

## References

* The Stacks Project, Lemma 20.11.9 (Cartan's criterion), whose proof is followed here, and
  Lemma 30.2.2 (tag 01XB), where it is applied to the standard opens of an affine scheme.
-/

public section

noncomputable section

open CategoryTheory Limits Opposite TopologicalSpace TauCeti.CategoryTheory

universe u

namespace TauCeti.Topology

variable {X : TopCat.{u}}

/-- A sheaf `F` of abelian groups on `X` is *Čech acyclic on* a set `B` of opens if for every
finite nonempty family `U i` of members of `B` and every member `Y` of `B` contained in their union,
the augmented Čech complex `0 ⟶ F(Y) ⟶ Č⁰(U, F(Y ∩ -)) ⟶ Č¹(U, F(Y ∩ -)) ⟶ ⋯` of the cover of `Y`
by the opens `Y ∩ U i` is exact. -/
def IsCechAcyclicOn (B : Set (Opens X))
    (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) : Prop :=
  ∀ ⦃ι : Type u⦄ [Finite ι] [Nonempty ι] (U : ι → Opens X) (Y : Opens X), Y ∈ B →
    (∀ i, U i ∈ B) → Y ≤ ⨆ i, U i →
      QuasiIso (cechAugmentation U isTerminalTop ((prod.functor.obj Y).op ⋙ F.obj))

variable {B : Set (Opens X)}

/-- Unfolding `IsCechAcyclicOn`: Čech acyclicity on `B` is the exactness of the augmented Čech
complexes of the finite covers of members of `B` by members of `B`. -/
theorem isCechAcyclicOn_iff {F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}} :
    IsCechAcyclicOn B F ↔
      ∀ ⦃ι : Type u⦄ [Finite ι] [Nonempty ι] (U : ι → Opens X) (Y : Opens X), Y ∈ B →
        (∀ i, U i ∈ B) → Y ≤ ⨆ i, U i →
          QuasiIso (cechAugmentation U isTerminalTop ((prod.functor.obj Y).op ⋙ F.obj)) :=
  Iff.rfl

/-- Let `B` be a set of opens containing, inside each of its members, a basis of the topology of
that member. Along an epimorphism of sheaves `π : F ⟶ G`, a section of `G` over a member `Y` of `B`
lifts, near every point of `Y`, on a member of `B` contained in `Y`. -/
theorem _root_.TopCat.Sheaf.exists_mem_lift_of_epi
    (hbasis : ∀ U ∈ B, ∀ V : Opens X, V ≤ U → ∀ x ∈ V, ∃ W ∈ B, x ∈ W ∧ W ≤ V)
    {F G : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}} (π : F ⟶ G) [Epi π]
    {Y : Opens X} (hY : Y ∈ B) (s : G.obj.obj (op Y)) (x : X) (hx : x ∈ Y) :
    ∃ V ∈ B, x ∈ V ∧ ∃ h : V ≤ Y, ∃ t : F.obj.obj (op V),
      π.hom.app (op V) t = G.obj.map (homOfLE h).op s := by
  have : Sheaf.IsLocallySurjective π := (Sheaf.isLocallySurjective_iff_epi' _ π).2 inferInstance
  obtain ⟨V, f, ⟨t, ht⟩, hxV⟩ :=
    Presheaf.imageSieve_mem (Opens.grothendieckTopology X) π.hom s x hx
  obtain ⟨W, hW, hxW, hWV⟩ := hbasis Y hY V f.le x hxV
  refine ⟨W, hW, hxW, hWV.trans f.le, F.obj.map (homOfLE hWV).op t, ?_⟩
  rw [← ConcreteCategory.comp_apply, π.hom.naturality, ConcreteCategory.comp_apply, ht,
    ← ConcreteCategory.comp_apply, ← G.obj.map_comp]
  rfl

variable (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})

/-- The sequence of presheaves `0 ⟶ F ⟶ I ⟶ G ⟶ 0`, where `F ⟶ I` is the chosen embedding into an
injective sheaf and `G` is the image presheaf of `I ⟶ Q`, for `Q` its cokernel sheaf. -/
private abbrev imageSeq : ShortComplex ((Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u}) :=
  ShortComplex.mk (Injective.ι F).hom (factorThruImage (cokernel.π (Injective.ι F)).hom) (by
    rw [← cancel_mono (image.ι _), Category.assoc, image.fac, zero_comp]
    exact ((injectiveCokernelSequence F).map (sheafToPresheaf _ AddCommGrpCat.{u})).zero)

/-- The sequence `0 ⟶ F ⟶ I ⟶ G ⟶ 0` is exact on every open: the kernel of `I(V) ⟶ Q(V)` is
`F(V)`, and `G(V)` is the image of `I(V)` in `Q(V)`. -/
private lemma imageSeq_shortExact (V : (Opens X)ᵒᵖ) :
    ((imageSeq F).map ((evaluation _ AddCommGrpCat.{u}).obj V)).ShortExact := by
  have hE := (injectiveCokernelSequence_shortExact F).exact.map_of_mono_of_preservesKernel
    (sheafToPresheaf _ AddCommGrpCat.{u} ⋙ (evaluation _ AddCommGrpCat.{u}).obj V)
    inferInstance inferInstance
  refine ShortComplex.ShortExact.mk' ?_ ?_ ?_
  · rw [ShortComplex.ab_exact_iff] at hE ⊢
    intro x hx
    apply hE x
    dsimp at hx ⊢
    have h := congrArg ((image.ι (cokernel.π (Injective.ι F)).hom).app V) hx
    rwa [← ConcreteCategory.comp_apply, ← NatTrans.comp_app, image.fac, map_zero] at h
  · exact Functor.map_mono (sheafToPresheaf _ AddCommGrpCat.{u} ⋙
      (evaluation _ AddCommGrpCat.{u}).obj V) (Injective.ι F)
  · dsimp
    infer_instance

variable {F}

/-- For `F` Čech acyclic on `B`, the image presheaf of `I ⟶ Q` is Čech acyclic for the finite
covers of members of `B` by members of `B`, like `F` and the flasque sheaf `I`. -/
private lemma quasiIso_cechAugmentation_image (hF : IsCechAcyclicOn B F) {ι : Type u} [Finite ι]
    [Nonempty ι] (U : ι → Opens X) {Y : Opens X} (hY : Y ∈ B) (hU : ∀ i, U i ∈ B)
    (hYU : Y ≤ ⨆ i, U i) :
    QuasiIso (cechAugmentation U isTerminalTop
      ((prod.functor.obj Y).op ⋙ Limits.image (cokernel.π (Injective.ι F)).hom)) := by
  have : TopCat.Presheaf.IsFlasque (TopCat.Sheaf.presheaf (Injective.under F)) :=
    isFlasque_of_injective (Injective.under F)
  exact quasiIso_cechAugmentation_X₃_of_shortExact U isTerminalTop
    ((imageSeq F).map ((Functor.whiskeringLeft _ _ AddCommGrpCat.{u}).obj
      (prod.functor.obj Y).op))
    (imageSeq_shortExact F _) (fun _ _ ↦ imageSeq_shortExact F _) (hF U Y hY hU hYU)
    (TopCat.Sheaf.quasiIso_cechAugmentation_prod_of_isFlasque (Injective.under F) U Y hYU)

/-- Let `π : F₂ ⟶ F₃` be a morphism of sheaves, `G` its image presheaf, and `U i` opens covering
`Y`. If `G` satisfies the sheaf condition for this cover, in the form of the exactness of its
augmented Čech complex in degree `0`, then sections `x i` of `G` over the opens `Y ⨯ U i`, whose
images in `F₃` are restrictions of a single section `s` of `F₃` over `Y`, glue to a section of `G`
over `Y ⨯ ⊤`. -/
private lemma exists_map_eq_of_cover
    {F₂ F₃ : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}} (π : F₂ ⟶ F₃) {ι : Type u}
    (U : ι → Opens X) {Y : Opens X}
    (hG : QuasiIso (cechAugmentation U isTerminalTop
      ((prod.functor.obj Y).op ⋙ Limits.image π.hom)))
    (s : F₃.obj.obj (op Y)) (x : ∀ i, (Limits.image π.hom).obj (op (Y ⨯ U i)))
    (hx : ∀ i {V : Opens X} (e : V ⟶ Y ⨯ U i),
      (image.ι π.hom).app (op V) ((Limits.image π.hom).map e.op (x i)) =
        F₃.obj.map (e ≫ prod.fst).op s) :
    ∃ g : (Limits.image π.hom).obj (op (Y ⨯ ⊤)), ∀ i (r : Y ⨯ U i ⟶ Y ⨯ ⊤),
      (Limits.image π.hom).map r.op g = x i := by
  have hι (V : (Opens X)ᵒᵖ) : Function.Injective ((image.ι π.hom).app V) :=
    (AddCommGrpCat.mono_iff_injective _).1 inferInstance
  have h := (Presieve.isSheafFor_comp_forget_addCommGrpCat_iff _ _).2
    ((quasiIsoAt_cechAugmentation_zero_iff U isTerminalTop _).1 (hG.quasiIsoAt 0))
  have hπ : (fun i ↦ isTerminalTop.from (U i)) = fun i ↦ homOfLE le_top :=
    funext fun _ ↦ Subsingleton.elim _ _
  rw [hπ, Presieve.isSheafFor_arrows_iff] at h
  obtain ⟨g, hg, -⟩ := h x ((Presieve.Arrows.compatible_homOfLE_iff
    (P := ((prod.functor.obj Y).op ⋙ Limits.image π.hom) ⋙ forget AddCommGrpCat)
    (fun _ ↦ le_top) x).2
    fun i j ↦ hι _ ((hx i ((prod.functor.obj Y).map (homOfLE inf_le_left))).trans
      (Eq.trans (congrArg (fun f ↦ F₃.obj.map (Quiver.Hom.op f) s) (Subsingleton.elim _ _))
        (hx j ((prod.functor.obj Y).map (homOfLE inf_le_right))).symm)))
  -- `hg i` is stated for the presheaf `(prod.functor.obj Y).op ⋙ G`, whose maps are those of `G`
  exact ⟨g, fun i r ↦ (congrArg (fun f ↦ (Limits.image π.hom).map (Quiver.Hom.op f) g)
    (Subsingleton.elim r ((prod.functor.obj Y).map (homOfLE le_top)))).trans (hg i)⟩

/-- Let `π : F₂ ⟶ F₃` be a morphism of sheaves, and let `U i` be opens covering `Y`. If the image
presheaf of `π` satisfies the sheaf condition for this cover, in the form of the exactness of its
augmented Čech complex in degree `0`, then a section of `F₃` over `Y` whose restrictions to the
`U i` lift to `F₂` lifts to `F₂` itself. -/
private lemma exists_eq_of_cover {F₂ F₃ : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}}
    (π : F₂ ⟶ F₃) {ι : Type u} (U : ι → Opens X) {Y : Opens X}
    (hUY : ∀ i, U i ≤ Y) (hYU : Y ≤ ⨆ i, U i)
    (hG : QuasiIso (cechAugmentation U isTerminalTop
      ((prod.functor.obj Y).op ⋙ Limits.image π.hom)))
    (s : F₃.obj.obj (op Y)) (t : ∀ i, F₂.obj.obj (op (U i)))
    (ht : ∀ i, π.hom.app (op (U i)) (t i) = F₃.obj.map (homOfLE (hUY i)).op s) :
    ∃ t' : F₂.obj.obj (op Y), π.hom.app (op Y) t' = s := by
  have hfac (V : (Opens X)ᵒᵖ) (y : F₂.obj.obj V) :
      (image.ι π.hom).app V ((factorThruImage π.hom).app V y) = π.hom.app V y := by
    rw [← ConcreteCategory.comp_apply, ← NatTrans.comp_app, image.fac]
  -- the lifts `t i`, restricted to `Y ⨯ U i`, as sections of the image presheaf
  let x (i : ι) : (Limits.image π.hom).obj (op (Y ⨯ U i)) :=
    (factorThruImage π.hom).app (op (Y ⨯ U i)) (F₂.obj.map (prod.snd : Y ⨯ U i ⟶ U i).op (t i))
  have hx (i : ι) {V : Opens X} (e : V ⟶ Y ⨯ U i) :
      (image.ι π.hom).app (op V) ((Limits.image π.hom).map e.op (x i)) =
        F₃.obj.map (e ≫ prod.fst).op s := by
    rw [NatTrans.naturality_apply]
    dsimp only [x]
    rw [hfac, NatTrans.naturality_apply, ht, ← Functor.map_comp_apply, ← Functor.map_comp_apply]
    exact congrArg (fun f ↦ F₃.obj.map (Quiver.Hom.op f) s) (Subsingleton.elim _ _)
  obtain ⟨g, hg⟩ := exists_map_eq_of_cover π U hG s x hx
  obtain ⟨t', rfl⟩ := (AddCommGrpCat.epi_iff_surjective _).1
    (inferInstance : Epi ((factorThruImage π.hom).app (op (Y ⨯ ⊤)))) g
  refine ⟨F₂.obj.map (prod.lift (𝟙 Y) (isTerminalTop.from Y)).op t', ?_⟩
  refine TopCat.Sheaf.eq_of_locally_eq' F₃ U Y (fun i ↦ homOfLE (hUY i)) hYU _ _ fun i ↦ ?_
  let e : U i ⟶ Y ⨯ U i := prod.lift (homOfLE (hUY i)) (𝟙 _)
  let r : Y ⨯ U i ⟶ Y ⨯ ⊤ := prod.map (𝟙 Y) (isTerminalTop.from (U i))
  calc F₃.obj.map (homOfLE (hUY i)).op (π.hom.app (op Y)
          (F₂.obj.map (prod.lift (𝟙 Y) (isTerminalTop.from Y)).op t'))
      _ = π.hom.app (op (U i)) (F₂.obj.map (e ≫ r).op t') := by
        rw [← NatTrans.naturality_apply π.hom, ← Functor.map_comp_apply, ← op_comp]
        exact congrArg (fun f ↦ π.hom.app _ (F₂.obj.map (Quiver.Hom.op f) t'))
          (Subsingleton.elim _ _)
      _ = (image.ι π.hom).app (op (U i)) ((Limits.image π.hom).map e.op
          ((Limits.image π.hom).map r.op ((factorThruImage π.hom).app (op (Y ⨯ ⊤)) t'))) := by
        rw [← NatTrans.naturality_apply (factorThruImage π.hom),
          ← NatTrans.naturality_apply (factorThruImage π.hom), hfac, op_comp,
          Functor.map_comp_apply]
      _ = F₃.obj.map (homOfLE (hUY i)).op s := by
        rw [hg i r, hx i e]
        exact congrArg (fun f ↦ F₃.obj.map (Quiver.Hom.op f) s) (Subsingleton.elim _ _)

section

variable (hinf : ∀ U ∈ B, ∀ V ∈ B, U ⊓ V ∈ B) (hcpt : ∀ U ∈ B, IsCompact (U : Set X))
  (hbasis : ∀ U ∈ B, ∀ V : Opens X, V ≤ U → ∀ x ∈ V, ∃ W ∈ B, x ∈ W ∧ W ≤ V)

include hinf in
/-- A set of opens closed under binary intersections contains the intersection of a member with
finitely many members. -/
private lemma inf_finsetInf_mem {ι : Type u} {U : ι → Opens X} (hU : ∀ i, U i ∈ B) {Y : Opens X}
    (hY : Y ∈ B) (s : Finset ι) : Y ⊓ s.inf U ∈ B := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hY
  | insert a s _ ih =>
    rw [Finset.inf_insert, inf_left_comm]
    exact hinf _ (hU a) _ ih

include hinf in
/-- If a set `B` of opens is closed under binary intersections, then the product of a member `Y`
with finitely many members `U (a 0), …, U (a n)`, which in the poset of opens is their
intersection, is again a member. -/
theorem prod_pi_mem_of_inf_mem {ι : Type u} {U : ι → Opens X} (hU : ∀ i, U i ∈ B) {Y : Opens X}
    (hY : Y ∈ B) (n : ℕ) (a : Fin (n + 1) → ι) : (Y ⨯ ∏ᶜ fun j ↦ U (a j)) ∈ B := by
  classical
  rw [CompleteLattice.prod_eq_inf, CompleteLattice.finite_product_eq_finset_image_inf]
  exact inf_finsetInf_mem hinf hU hY _

include hcpt hbasis in
/-- For `F` Čech acyclic on `B`, sections of the cokernel `Q` of the chosen embedding `F ⟶ I` into
an injective sheaf lift to `I` over every member of `B`. -/
private lemma surjective_app_cokernel_π (hF : IsCechAcyclicOn B F) {Y : Opens X} (hY : Y ∈ B) :
    Function.Surjective ((cokernel.π (Injective.ι F)).hom.app (op Y)) := by
  intro s
  choose V hVB hxV hVY t ht using fun x : Y ↦
    TopCat.Sheaf.exists_mem_lift_of_epi hbasis (cokernel.π (Injective.ι F)) hY s x.1 x.2
  obtain ⟨c, hc⟩ := (hcpt Y hY).elim_finite_subcover (fun x : Y ↦ (V x : Set X))
    (fun x ↦ (V x).isOpen) (fun x hx ↦ Set.mem_iUnion.2 ⟨⟨x, hx⟩, hxV _⟩)
  -- an empty subcover only covers the empty open, over which every section vanishes
  cases isEmpty_or_nonempty c with
  | inl _ =>
    have hY₀ : Y = ⊥ := eq_bot_iff.2 fun y hy ↦ by
      obtain ⟨x, hx, -⟩ := Set.mem_iUnion₂.1 (hc hy)
      exact isEmptyElim (⟨x, hx⟩ : c)
    have := AddCommGrpCat.subsingleton_of_isZero ((isZero_zero _).of_iso
      ((isZero_zero _).isoIsTerminal
        (TopCat.Sheaf.isTerminalOfEqEmpty (cokernel (Injective.ι F)) hY₀)).symm)
    exact ⟨0, @Subsingleton.elim _ this _ _⟩
  | inr _ => ?_
  let U : c → Opens X := fun x ↦ V x
  have hYU : Y ≤ ⨆ x, U x := by
    intro y hy
    obtain ⟨x, hx, hyx⟩ := Set.mem_iUnion₂.1 (hc hy)
    exact Opens.mem_iSup.2 ⟨⟨x, hx⟩, hyx⟩
  exact exists_eq_of_cover _ U (fun x ↦ hVY x) hYU
    (quasiIso_cechAugmentation_image hF U hY (fun x ↦ hVB x) hYU) s (fun x ↦ t x)
    (fun x ↦ ht x)

include hcpt hbasis in
/-- A sheaf which is Čech acyclic on `B` has no degree one cohomology on the members of `B`. -/
private lemma subsingleton_H'_one (hF : IsCechAcyclicOn B F) {Y : Opens X} (hY : Y ∈ B) :
    Subsingleton (F.H' 1 Y) :=
  Sheaf.H'.subsingleton_X₁_one (injectiveCokernelSequence_shortExact F) Y
    (surjective_app_cokernel_π hcpt hbasis hF hY)
    (subsingleton_H'_succ_of_isFlasque (Injective.under F) 0 Y)

include hinf hcpt hbasis in
/-- The cokernel `Q` of the chosen embedding of a sheaf `F` which is Čech acyclic on `B` into an
injective sheaf is again Čech acyclic on `B`. -/
private lemma isCechAcyclicOn_cokernel (hF : IsCechAcyclicOn B F) :
    IsCechAcyclicOn B (cokernel (Injective.ι F)) := by
  intro ι _ _ U Y hY hU hYU
  have : TopCat.Presheaf.IsFlasque (TopCat.Sheaf.presheaf (Injective.under F)) :=
    isFlasque_of_injective (Injective.under F)
  have hS (V : Opens X) (hV : V ∈ B) :=
    Sheaf.H'.shortExact_map_sheafSections (injectiveCokernelSequence_shortExact F) V
      (subsingleton_H'_one hcpt hbasis hF hV)
  exact quasiIso_cechAugmentation_X₃_of_shortExact U isTerminalTop
    (((injectiveCokernelSequence F).map (sheafToPresheaf _ AddCommGrpCat.{u})).map
      ((Functor.whiskeringLeft _ _ AddCommGrpCat.{u}).obj (prod.functor.obj Y).op))
    (hS _ (by simpa [CompleteLattice.prod_eq_inf] using hY))
    (fun n a ↦ hS _ (prod_pi_mem_of_inf_mem hinf hU hY n a)) (hF U Y hY hU hYU)
    (TopCat.Sheaf.quasiIso_cechAugmentation_prod_of_isFlasque (Injective.under F) U Y hYU)

include hinf hcpt hbasis in
/-- **Cartan's criterion.** Let `B` be a set of quasi-compact opens of `X` which is closed under
binary intersections and contains, inside each of its members, a basis of the topology of that
member. A sheaf of abelian groups which is Čech acyclic for the finite covers of members of `B` by
members of `B` has no cohomology in positive degrees on the members of `B`. -/
theorem subsingleton_H'_succ_of_isCechAcyclicOn (hF : IsCechAcyclicOn B F) {Y : Opens X}
    (hY : Y ∈ B) (n : ℕ) : Subsingleton (F.H' (n + 1) Y) := by
  induction n generalizing F with
  | zero => exact subsingleton_H'_one hcpt hbasis hF hY
  | succ n ih =>
    exact Sheaf.H'.subsingleton_X₁ (injectiveCokernelSequence_shortExact F) Y (n + 1)
      (ih (isCechAcyclicOn_cokernel hinf hcpt hbasis hF))
      (subsingleton_H'_succ_of_isFlasque (Injective.under F) (n + 1) Y)

end

end TauCeti.Topology
