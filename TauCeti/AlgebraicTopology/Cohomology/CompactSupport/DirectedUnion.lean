/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Category.TopCat.Opens
public import TauCeti.AlgebraicTopology.Cohomology.CompactSupport.Extension

/-!
# Cohomology with compact supports of a directed union of open sets

Extension along the inclusions of open subsets makes `V ↦ Hⁿ_c(V)` a functor on the open subsets of
a Hausdorff space `X` (`TopCat.compactSupportCohomologyOpens`), with a cocone to `Hⁿ_c(X)`
(`TopCat.compactSupportCohomologyOpensCocone`). If `X` is the union of a directed family of open
sets `U i`, then `Hⁿ_c(X)` is the colimit of the groups `Hⁿ_c(U i)`
(`TopCat.isColimitCompactSupportCohomologyOpensCocone`).

Both halves of the proof rest on compactness. A class of `Hⁿ_c(X)` comes from `Hⁿ(X, X ∖ K)` for
some compact `K`, and `K` lies in some `U i`, so the class is extended from `Hⁿ_c(U i)`
(`TopCat.exists_compactSupportCohomologyExtend_eq`,
`TopCat.exists_compactSupportCohomologyExtend_eq_of_iSup_eq_top`). A class of `Hⁿ_c(U i)` whose
extension vanishes dies in some `Hⁿ(X, X ∖ L)` with `L` compact, and `L` lies in some `U j` with
`i ≤ j`; excision for the compact set `L` inside `U j` shows that the class already vanishes in
`Hⁿ_c(U j)`
(`TopCat.compactSupportCohomologyι_eq_zero_of_restrict_eq_zero`,
`TopCat.exists_compactSupportCohomologyExtend_map_eq_zero_of_iSup_eq_top`).

This is the step of the proof of Poincaré duality that passes to increasing unions of open subsets
of a manifold.

## Main definitions and results

* `TopCat.compactSupportCohomologyOpens`: the functor `V ↦ Hⁿ_c(V)` on the open subsets of `X`.
* `TopCat.compactSupportCohomologyOpensCocone`: its cocone to `Hⁿ_c(X)`, by extension.
* `TopCat.exists_compactSupportCohomologyExtend_eq_of_iSup_eq_top` and
  `TopCat.exists_compactSupportCohomologyExtend_map_eq_zero_of_iSup_eq_top`: the description of the
  elements of the colimit over a directed open cover.
* `TopCat.isColimitCompactSupportCohomologyOpensCocone`: `Hⁿ_c(X) = colim_i Hⁿ_c(U i)`.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 3.3, step (3) of the proof of Lemma 3.36 (compactly supported cohomology of an
  increasing union of open sets is the direct limit).
-/

public section

noncomputable section

open CategoryTheory Limits TopologicalSpace Topology Opens

universe v u

namespace TopologicalSpace.Opens

variable {X : TopCat.{v}}

/-- The inclusion of an open set `V` into a larger open set `W` is an open embedding. -/
lemma isOpenEmbedding_toTopCat_map {V W : Opens X} (h : V ⟶ W) :
    IsOpenEmbedding ((toTopCat X).map h) :=
  IsOpenEmbedding.of_comp _ W.isOpenEmbedding V.isOpenEmbedding

/-- The inclusion of `V` into `W` followed by the inclusion of `W` is the inclusion of `V`. -/
@[reassoc (attr := simp)]
lemma toTopCat_map_comp_inclusion' {V W : Opens X} (h : V ⟶ W) :
    (toTopCat X).map h ≫ inclusion' W = inclusion' V :=
  rfl

/-- An open subset of a Hausdorff space is Hausdorff. -/
instance t2Space_toTopCat_obj [T2Space X] (V : Opens X) : T2Space ((toTopCat X).obj V) :=
  inferInstanceAs (T2Space V)

end TopologicalSpace.Opens

namespace TopCat

variable {C : Type u} [Category.{v} C] [HasCoproducts.{v} C] [Abelian C] {R : C}
  {k : Type v} [Ring k] [Linear k C] {M : C} {X : TopCat.{v}}

/-! ### Extension along one open embedding -/

/-- Restricting along the identity of `X` from `X ∖ K` to `X ∖ L` and then to `X ∖ N` is the
restriction from `X ∖ K` to `X ∖ N`. -/
private lemma singularCohomologyMap_ofSubsetMap_id_trans {K L N : Compacts X} (h₁ : K ≤ L)
    (h₂ : L ≤ N) (n : ℕ) :
    TopPair.singularCohomologyMap (R := R) (k := k) (M := M)
        (TopPair.ofSubsetMap (𝟙 X) (mapsTo_id_compl_compacts h₁)) n ≫
      TopPair.singularCohomologyMap (TopPair.ofSubsetMap (𝟙 X) (mapsTo_id_compl_compacts h₂)) n =
    TopPair.singularCohomologyMap
      (TopPair.ofSubsetMap (𝟙 X) (mapsTo_id_compl_compacts (h₁.trans h₂))) n :=
  ((X.compactSupportCohomologyDiagram R k M n).map_comp (homOfLE h₁) (homOfLE h₂)).symm

section OpenEmbedding

variable {U : TopCat.{v}} [T2Space X]

/-- A class of `Hⁿ(X, X ∖ K)` with `K` inside the image of an open embedding `f : U ⟶ X` is, with
compact support, the extension of a compactly supported class of `U`. -/
theorem exists_compactSupportCohomologyExtend_eq {f : U ⟶ X} (hf : IsOpenEmbedding f) {n : ℕ}
    {K : Compacts X} (hK : (K : Set X) ⊆ Set.range f)
    (y : (TopPair.ofSubset (K : Set X)ᶜ).singularCohomology R k M n) :
    ∃ z, compactSupportCohomologyExtend hf n z = compactSupportCohomologyι n K y := by
  let K' : Compacts U := ⟨f ⁻¹' K, hf.isInducing.isCompact_preimage' K.isCompact hK⟩
  have hle : K ≤ K'.map f f.hom.continuous := fun x hx ↦ by
    obtain ⟨u, rfl⟩ := hK hx
    exact ⟨u, hx, rfl⟩
  refine ⟨compactSupportCohomologyι n K' (TopPair.singularCohomologyMap
    (TopPair.ofSubsetMap f (mapsTo_compl_compacts_map hf.injective K')) n
      (TopPair.singularCohomologyMap (TopPair.ofSubsetMap (𝟙 X)
        (mapsTo_id_compl_compacts hle)) n y)), ?_⟩
  rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply,
    singularCohomologyMap_comp_compactSupportCohomologyι_comp_extend,
    singularCohomologyMap_comp_compactSupportCohomologyι_apply n hle]

/-- A class of `Hⁿ(U, U ∖ K)` vanishes with compact support in `U` once its excision to
`Hⁿ(X, X ∖ f(K))` along an open embedding `f : U ⟶ X` restricts to zero in `Hⁿ(X, X ∖ L)` for a
compact `L` inside the image of `f`. -/
theorem compactSupportCohomologyι_eq_zero_of_restrict_eq_zero {f : U ⟶ X}
    (hf : IsOpenEmbedding f) {n : ℕ} {K : Compacts U}
    (y : (TopPair.ofSubset (K : Set U)ᶜ).singularCohomology R k M n) {L : Compacts X}
    (hKL : K.map f f.hom.continuous ≤ L) (hL : (L : Set X) ⊆ Set.range f)
    (hy : TopPair.singularCohomologyMap (TopPair.ofSubsetMap (𝟙 X) (mapsTo_id_compl_compacts hKL))
      n ((singularCohomologyComplCompactsMapIso R k M hf K n).inv y) = 0) :
    compactSupportCohomologyι n K y = 0 := by
  let L' : Compacts U := ⟨f ⁻¹' L, hf.isInducing.isCompact_preimage' L.isCompact hL⟩
  have hKL' : K ≤ L' := fun x hx ↦ hKL ⟨x, hx, rfl⟩
  have hLL' : L ≤ L'.map f f.hom.continuous := fun x hx ↦ by
    obtain ⟨u, rfl⟩ := hL hx
    exact ⟨u, hx, rfl⟩
  rw [compactSupportCohomologyι_eq_zero_iff]
  refine ⟨L', hKL', ?_⟩
  have h := ConcreteCategory.congr_hom (singularCohomologyComplCompactsMapIso_inv_naturality
    (R := R) (k := k) (M := M) hf hKL' n) y
  rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply,
    ← singularCohomologyMap_ofSubsetMap_id_trans hKL hLL', ConcreteCategory.comp_apply, hy,
    map_zero] at h
  have h' := congr((singularCohomologyComplCompactsMapIso R k M hf L' n).hom $h)
  rwa [Iso.inv_hom_id_apply, map_zero] at h'

/-- Extensions along equal open embeddings are equal. -/
lemma compactSupportCohomologyExtend_congr {f g : U ⟶ X} (h : f = g) (hf : IsOpenEmbedding f)
    (hg : IsOpenEmbedding g) (n : ℕ) :
    compactSupportCohomologyExtend (R := R) (k := k) (M := M) hf n =
      compactSupportCohomologyExtend hg n := by
  subst h
  rfl

end OpenEmbedding

/-! ### Open subsets -/

variable [T2Space X]

variable (R k M X) in
/-- Cohomology with compact supports on the open subsets of a Hausdorff space `X`, as a functor
`V ↦ Hⁿ_c(V)` along the extensions by zero. -/
@[expose, simps]
def compactSupportCohomologyOpens (n : ℕ) : Opens X ⥤ ModuleCat.{v} k where
  obj V := ((toTopCat X).obj V).compactSupportCohomology R k M n
  map h := compactSupportCohomologyExtend (isOpenEmbedding_toTopCat_map h) n
  map_id V := (compactSupportCohomologyExtend_congr ((toTopCat X).map_id V) _
    (by simpa using IsOpenEmbedding.id) n).trans (compactSupportCohomologyExtend_id n _)
  map_comp h₁ h₂ := (compactSupportCohomologyExtend_congr ((toTopCat X).map_comp h₁ h₂) _
    ((isOpenEmbedding_toTopCat_map h₂).comp (isOpenEmbedding_toTopCat_map h₁)) n).trans
      (compactSupportCohomologyExtend_comp (isOpenEmbedding_toTopCat_map h₁)
        (isOpenEmbedding_toTopCat_map h₂) n _)

variable (R k M X) in
/-- The cocone of the extensions `Hⁿ_c(V) ⟶ Hⁿ_c(X)` along the inclusions of the open subsets
`V` of a Hausdorff space `X`. -/
@[expose, simps]
def compactSupportCohomologyOpensCocone (n : ℕ) : Cocone (compactSupportCohomologyOpens R k M X n)
    where
  pt := X.compactSupportCohomology R k M n
  ι :=
    { app V := compactSupportCohomologyExtend V.isOpenEmbedding n
      naturality _ W h :=
        ((compactSupportCohomologyExtend_comp (isOpenEmbedding_toTopCat_map h) W.isOpenEmbedding n
          (W.isOpenEmbedding.comp (isOpenEmbedding_toTopCat_map h))).symm.trans
          (compactSupportCohomologyExtend_congr (toTopCat_map_comp_inclusion' h) _ _ n)).trans
          (Category.comp_id _).symm }

/-! ### Directed unions -/

variable {ι : Type*} [Preorder ι] [IsDirected ι (· ≤ ·)] [Nonempty ι] {U : ι → Opens X}

omit [T2Space X] in
/-- A compact subset of the union of a directed family of open sets lies in one of them. -/
private lemma exists_compacts_le_of_iSup_eq_top (hU : Monotone U) (hcover : ⨆ i, U i = ⊤)
    (K : Compacts X) : ∃ i, (K : Set X) ⊆ U i :=
  K.isCompact.elim_directed_cover (fun i ↦ (U i : Set X)) (fun i ↦ (U i).isOpen)
    (fun x _ ↦ by simp [← Opens.coe_iSup, hcover])
    (hU.directed_le.mono_comp _ fun _ _ h ↦ h)

/-- **Every compactly supported class of a directed open union comes from a member.** -/
theorem exists_compactSupportCohomologyExtend_eq_of_iSup_eq_top (hU : Monotone U)
    (hcover : ⨆ i, U i = ⊤) {n : ℕ} (x : X.compactSupportCohomology R k M n) :
    ∃ i z, compactSupportCohomologyExtend (U i).isOpenEmbedding n z = x := by
  obtain ⟨K, -, y, rfl⟩ := exists_compactSupportCohomologyι_eq x ⊥
  obtain ⟨i, hi⟩ := exists_compacts_le_of_iSup_eq_top hU hcover K
  obtain ⟨z, hz⟩ := exists_compactSupportCohomologyExtend_eq (U i).isOpenEmbedding
    (fun x hx ↦ ⟨⟨x, hi hx⟩, rfl⟩) y
  exact ⟨i, z, hz⟩

/-- **A compactly supported class of a member of a directed open union whose extension vanishes
already vanishes in a larger member.** -/
theorem exists_compactSupportCohomologyExtend_map_eq_zero_of_iSup_eq_top (hU : Monotone U)
    (hcover : ⨆ i, U i = ⊤) {n : ℕ} {i : ι}
    (z : ((toTopCat X).obj (U i)).compactSupportCohomology R k M n)
    (hz : compactSupportCohomologyExtend (U i).isOpenEmbedding n z = 0) :
    ∃ (j : ι) (hij : i ≤ j),
      compactSupportCohomologyExtend (isOpenEmbedding_toTopCat_map (homOfLE (hU hij))) n z = 0 := by
  obtain ⟨K, -, y, rfl⟩ := exists_compactSupportCohomologyι_eq z ⊥
  rw [← ConcreteCategory.comp_apply, compactSupportCohomologyι_comp_extend,
    ConcreteCategory.comp_apply, compactSupportCohomologyι_eq_zero_iff] at hz
  obtain ⟨L, hKL, hL⟩ := hz
  obtain ⟨j₀, hj₀⟩ := exists_compacts_le_of_iSup_eq_top hU hcover L
  obtain ⟨j, hij, hj₀j⟩ := exists_ge_ge i j₀
  refine ⟨j, hij, ?_⟩
  let g := (toTopCat X).map (homOfLE (hU hij))
  have hg := isOpenEmbedding_toTopCat_map (homOfLE (hU hij))
  -- the two images of `K` in `X`, directly and through `U j`, are the same compact set
  have hle : K.map (inclusion' (U i)) (inclusion' (U i)).hom.continuous ≤
      (K.map g g.hom.continuous).map (inclusion' (U j))
        (inclusion' (U j)).hom.continuous := fun x hx ↦ by
    obtain ⟨y, hy, rfl⟩ := hx
    exact ⟨g y, ⟨y, hy, rfl⟩, rfl⟩
  have hK₂L : (K.map g g.hom.continuous).map (inclusion' (U j))
      (inclusion' (U j)).hom.continuous ≤ L := fun x hx ↦ by
    obtain ⟨-, ⟨y, hy, rfl⟩, rfl⟩ := hx
    exact hKL ⟨y, hy, rfl⟩
  -- excising `K` from `U j` and then from `U i` is excising it from `X`
  have hcomp : TopPair.singularCohomologyMap
        (TopPair.ofSubsetMap (𝟙 X) (mapsTo_id_compl_compacts hle)) n ≫
      (singularCohomologyComplCompactsMapIso R k M (U j).isOpenEmbedding
        (K.map g g.hom.continuous) n).hom ≫
          (singularCohomologyComplCompactsMapIso R k M hg K n).hom =
      (singularCohomologyComplCompactsMapIso R k M (U i).isOpenEmbedding K n).hom :=
    singularCohomologyComplCompactsMapIso_hom_comp hg (U j).isOpenEmbedding
      (U i).isOpenEmbedding K hle n
  have hinv : (singularCohomologyComplCompactsMapIso R k M hg K n).inv ≫
      (singularCohomologyComplCompactsMapIso R k M (U j).isOpenEmbedding
        (K.map g g.hom.continuous) n).inv =
      (singularCohomologyComplCompactsMapIso R k M (U i).isOpenEmbedding K n).inv ≫
        TopPair.singularCohomologyMap
          (TopPair.ofSubsetMap (𝟙 X) (mapsTo_id_compl_compacts hle)) n := by
    rw [Iso.eq_inv_comp, ← hcomp]
    simp only [Category.assoc, Iso.hom_inv_id_assoc, Iso.hom_inv_id, Category.comp_id]
  rw [← ConcreteCategory.comp_apply, compactSupportCohomologyι_comp_extend,
    ConcreteCategory.comp_apply]
  refine compactSupportCohomologyι_eq_zero_of_restrict_eq_zero (U j).isOpenEmbedding _ hK₂L
    (fun x hx ↦ ⟨⟨x, hU hj₀j (hj₀ hx)⟩, rfl⟩) ?_
  rw [← ConcreteCategory.comp_apply (singularCohomologyComplCompactsMapIso R k M hg K n).inv, hinv,
    ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply,
    singularCohomologyMap_ofSubsetMap_id_trans hle hK₂L]
  exact hL

/-- **Cohomology with compact supports of a directed open union.** If a Hausdorff space `X` is the
union of a directed family of open sets `U i`, then `Hⁿ_c(X)` is the colimit of the groups
`Hⁿ_c(U i)` along the extensions. -/
def isColimitCompactSupportCohomologyOpensCocone {J : Type v} [Preorder J]
    [IsDirected J (· ≤ ·)] [Nonempty J] {V : J → Opens X} (hV : Monotone V)
    (hcover : ⨆ j, V j = ⊤) (n : ℕ) :
    IsColimit ((compactSupportCohomologyOpensCocone R k M X n).whisker hV.functor) := by
  apply isColimitOfReflects (forget (ModuleCat.{v} k))
  refine Types.FilteredColimit.isColimitOf' _ _ (fun x ↦ ?_) (fun i x y hxy ↦ ?_)
  · obtain ⟨i, z, rfl⟩ := exists_compactSupportCohomologyExtend_eq_of_iSup_eq_top hV hcover x
    exact ⟨i, z, rfl⟩
  · -- the elements of the forgotten diagram, as elements of the modules `Hⁿ_c(V i)`
    let x' : ((toTopCat X).obj (V i)).compactSupportCohomology R k M n := x
    let y' : ((toTopCat X).obj (V i)).compactSupportCohomology R k M n := y
    obtain ⟨j, hij, h⟩ :=
      exists_compactSupportCohomologyExtend_map_eq_zero_of_iSup_eq_top hV hcover (x' - y')
        (by rw [map_sub, sub_eq_zero]; exact hxy)
    rw [map_sub, sub_eq_zero] at h
    exact ⟨j, homOfLE hij, h⟩

end TopCat
