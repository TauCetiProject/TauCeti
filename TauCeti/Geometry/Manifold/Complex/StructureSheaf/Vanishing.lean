/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Complex.StructureSheaf.Basic
public import Mathlib.RingTheory.Ideal.Operations
import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing
import Mathlib.Algebra.Category.Ring.FilteredColimits

/-!
# Holomorphic sections with prescribed vanishing

A finitely supported multiplicity function prescribes, at each point, a power of the ideal of
holomorphic germs vanishing there. The holomorphic sections whose germs belong to these powers
form an ideal on every open set and a sheaf of complex vector spaces. On a complex curve this is
the ideal-sheaf construction of the negative of the corresponding effective divisor.

`vanishingIdeal` gives the section ideals, and `vanishingSheaf` assembles their restrictions
and gluings. The construction is intrinsic: it uses stalk evaluation rather than chosen
coordinates. At a divisor consisting of one point with multiplicity one, the section ideal
is exactly the kernel of evaluation at that point. Increasing the divisor shrinks the ideals,
and away from its support every holomorphic section is allowed.
These sheaves supply the negative-divisor terms in exact sequences of divisor sheaves.

## References

* Otto Forster, *Lectures on Riemann Surfaces*, §§6 and 16.
* The stalkwise construction follows Mathlib's
  `TopCat.Presheaf.submonoidPresheafOfStalk`, by Kim Morrison and Andrew Yang, replacing
  submonoids by powers of the kernels of holomorphic stalk evaluation.
-/

public noncomputable section

open CategoryTheory Opposite TopologicalSpace
open scoped ContDiff Manifold

namespace TauCeti.holomorphicStructureSheaf

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℂ E H)
  (X : Type) [TopologicalSpace X] [ChartedSpace H X]

/-- The ideal of holomorphic sections vanishing to finitely supported multiplicities.
At `x`, the germ must lie in the `D x`-th power of the stalk evaluation kernel. -/
def vanishingIdeal (D : X →₀ ℕ) (U : Opens X) :
    Ideal ((holomorphicStructureSheaf I X).obj.obj (op U)) :=
  ⨅ x : U, Ideal.comap ((holomorphicStructureSheaf I X).presheaf.germ U x x.2).hom
    ((RingHom.ker (eval I X x)) ^ D x)

/-- The section ideal is the intersection of the inverse images of the prescribed stalk powers. -/
theorem vanishingIdeal_def (D : X →₀ ℕ) (U : Opens X) :
    vanishingIdeal I X D U =
      ⨅ x : U, Ideal.comap ((holomorphicStructureSheaf I X).presheaf.germ U x x.2).hom
        ((RingHom.ker (eval I X x)) ^ D x) := (rfl)

/-- Membership in the section ideal is checked on the germs at the points of the open set. -/
@[simp]
theorem mem_vanishingIdeal (D : X →₀ ℕ) (U : Opens X)
    (f : (holomorphicStructureSheaf I X).obj.obj (op U)) :
    f ∈ vanishingIdeal I X D U ↔ ∀ x : U,
      (holomorphicStructureSheaf I X).presheaf.germ U x x.2 f ∈
        (RingHom.ker (eval I X x)) ^ D x := by
  simp [vanishingIdeal]

/-- Restriction preserves the prescribed vanishing of germs. -/
theorem map_mem_vanishingIdeal (D : X →₀ ℕ) {U V : Opens X} (h : V ⟶ U)
    {f : (holomorphicStructureSheaf I X).obj.obj (op U)}
    (hf : f ∈ vanishingIdeal I X D U) :
    (holomorphicStructureSheaf I X).obj.map h.op f ∈ vanishingIdeal I X D V := by
  rw [mem_vanishingIdeal] at hf ⊢
  intro x
  rw [TopCat.Presheaf.germ_res_apply]
  exact hf ⟨x, h.le x.2⟩

/-- The zero divisor imposes no vanishing condition. -/
@[simp]
theorem vanishingIdeal_zero (U : Opens X) : vanishingIdeal I X 0 U = ⊤ := by
  ext f
  rw [mem_vanishingIdeal]
  simp

/-- Off the support of the divisor the vanishing ideal is the whole section ring. -/
theorem vanishingIdeal_eq_top (D : X →₀ ℕ) (U : Opens X)
    (hD : ∀ x : U, D x = 0) : vanishingIdeal I X D U = ⊤ := by
  ext f
  rw [mem_vanishingIdeal]
  simp [hD]

/-- Increasing multiplicities strengthens the vanishing condition. -/
theorem vanishingIdeal_antitone (U : Opens X) : Antitone (fun D ↦ vanishingIdeal I X D U) := by
  intro D D' h f hf
  rw [mem_vanishingIdeal] at hf ⊢
  intro x
  exact Ideal.pow_le_pow_right (h x) (hf x)

/-- At a point in the support, every allowed section vanishes. -/
theorem apply_eq_zero_of_mem_vanishingIdeal (D : X →₀ ℕ) (U : Opens X)
    {f : (holomorphicStructureSheaf I X).obj.obj (op U)}
    (hf : f ∈ vanishingIdeal I X D U) (x : U) (hx : D x ≠ 0) : f x = 0 := by
  have hg := Ideal.pow_le_self hx ((mem_vanishingIdeal I X D U f).mp hf x)
  simpa only [RingHom.mem_ker, eval_germ] using hg

/-- A divisor supported at one point imposes only its stalk-ideal power condition there. -/
@[simp]
theorem vanishingIdeal_single (p : X) (n : ℕ) (U : Opens X) :
    vanishingIdeal I X (Finsupp.single p n) U =
      ⨅ hp : p ∈ U, Ideal.comap ((holomorphicStructureSheaf I X).presheaf.germ U p hp).hom
        ((RingHom.ker (eval I X p)) ^ n) := by
  classical
  ext f
  rw [mem_vanishingIdeal]
  simp only [Ideal.mem_iInf, Ideal.mem_comap]
  constructor
  · intro hf hp
    simpa only [Finsupp.single_eq_same] using hf ⟨p, hp⟩
  · intro hf x
    by_cases hx : x.1 = p
    · subst p
      simpa only [Finsupp.single_eq_same] using hf x.2
    · simp [Finsupp.single_eq_of_ne hx]

/-- A point with multiplicity one imposes precisely evaluation-zero on sections. -/
theorem mem_vanishingIdeal_single_one (p : X) (U : Opens X)
    (f : (holomorphicStructureSheaf I X).obj.obj (op U)) :
    f ∈ vanishingIdeal I X (Finsupp.single p 1) U ↔ ∀ hp : p ∈ U, f ⟨p, hp⟩ = 0 := by
  rw [vanishingIdeal_single]
  simp only [Ideal.mem_iInf, Ideal.mem_comap, pow_one, RingHom.mem_ker, eval_germ]

/-- The restriction map on holomorphic sections with the given vanishing conditions. -/
private def vanishingRestrict (D : X →₀ ℕ) {U V : Opens X} (h : V ⟶ U) :
    vanishingIdeal I X D U →ₗ[ℂ] vanishingIdeal I X D V where
  toFun f := ⟨(holomorphicStructureSheaf I X).obj.map h.op f.1,
    map_mem_vanishingIdeal I X D h f.2⟩
  map_add' _ _ := Subtype.ext (map_add _ _ _)
  map_smul' c f := by
    apply Subtype.ext
    apply holomorphicStructureSheaf.ext
    intro x
    simp [map_apply, smul_apply]

@[simp]
private theorem coe_vanishingRestrict (D : X →₀ ℕ) {U V : Opens X} (h : V ⟶ U)
    (f : vanishingIdeal I X D U) :
    (vanishingRestrict I X D h f).1 = (holomorphicStructureSheaf I X).obj.map h.op f.1 := (rfl)

/-- The presheaf of complex vector spaces of holomorphic sections with prescribed vanishing. -/
private def vanishingPresheaf (D : X →₀ ℕ) :
    TopCat.Presheaf (ModuleCat ℂ) (TopCat.of X) where
  obj U := ModuleCat.of ℂ (vanishingIdeal I X D U.unop)
  map h := ModuleCat.ofHom (vanishingRestrict I X D h.unop)
  map_id _ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro f
    apply Subtype.ext
    simp [vanishingRestrict]
  map_comp _ _ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro f
    apply Subtype.ext
    simp [vanishingRestrict]

/-- Holomorphic sections with prescribed germ vanishing glue uniquely. -/
private theorem vanishingPresheaf_isSheaf (D : X →₀ ℕ) :
    (vanishingPresheaf I X D).IsSheaf := by
  rw [TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing]
  intro ι U f hf
  have hc : TopCat.Presheaf.IsCompatible (holomorphicStructureSheaf I X).obj
      U (fun i ↦ (f i).1) := by
    intro i j
    exact congrArg Subtype.val (hf i j)
  obtain ⟨s, hs, hu⟩ := TopCat.Presheaf.IsSheaf.isSheafUniqueGluing
    (holomorphicStructureSheaf I X).property U (fun i ↦ (f i).1) hc
  have hmem : s ∈ vanishingIdeal I X D (iSup U) := by
    rw [mem_vanishingIdeal]
    intro x
    obtain ⟨i, hi⟩ := (Opens.mem_iSup.mp x.2)
    have hg := (mem_vanishingIdeal I X D (U i) (f i).1).mp (f i).2 ⟨x, hi⟩
    have hsi : (holomorphicStructureSheaf I X).obj.map (Opens.leSupr U i).op s = (f i).1 := hs i
    rw [← hsi] at hg
    rw [TopCat.Presheaf.germ_res_apply] at hg
    exact hg
  refine ⟨⟨s, hmem⟩, fun i ↦ Subtype.ext (hs i), ?_⟩
  intro t ht
  exact Subtype.ext (hu t.1 (fun i ↦ congrArg Subtype.val (ht i)))

/-- The sheaf of complex vector spaces of holomorphic sections whose germs vanish to the
multiplicities prescribed by a finitely supported function. -/
def vanishingSheaf (D : X →₀ ℕ) : TopCat.Sheaf (ModuleCat ℂ) (TopCat.of X) :=
  ⟨vanishingPresheaf I X D, vanishingPresheaf_isSheaf I X D⟩

/-- The sections of the vanishing sheaf are the corresponding section ideal. -/
theorem vanishingSheaf_obj (D : X →₀ ℕ) (U : Opens X) :
    (vanishingSheaf I X D).obj.obj (op U) = ModuleCat.of ℂ (vanishingIdeal I X D U) := (rfl)

/-- Read a section of the vanishing sheaf as a holomorphic section in its section ideal. -/
def vanishingSheafSectionsEquiv (D : X →₀ ℕ) (U : Opens X) :
    (vanishingSheaf I X D).obj.obj (op U) ≃ₗ[ℂ] vanishingIdeal I X D U :=
  LinearEquiv.refl ℂ _

/-- Reading sections in the section ideals commutes with restriction. -/
@[simp]
theorem vanishingSheafSectionsEquiv_map (D : X →₀ ℕ) {U V : Opens X} (h : V ⟶ U)
    (f : (vanishingSheaf I X D).obj.obj (op U)) :
    (vanishingSheafSectionsEquiv I X D V ((vanishingSheaf I X D).obj.map h.op f)).1 =
      (holomorphicStructureSheaf I X).obj.map h.op (vanishingSheafSectionsEquiv I X D U f).1 :=
  (rfl)

/-- The vanishing sheaf includes into the holomorphic structure sheaf as complex vector spaces. -/
def vanishingSheafι (D : X →₀ ℕ) :
    vanishingSheaf I X D ⟶ holomorphicStructureSheafModules I X where
  hom.app U := ModuleCat.ofHom <|
    (holomorphicStructureSheafModules.sectionsLinearEquiv I X U).symm.toLinearMap.comp
      ((vanishingIdeal I X D U.unop).restrictScalars ℂ).subtype
  hom.naturality := by
    intro U V h
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro f
    apply holomorphicStructureSheafModules.ext
    intro x
    -- Erase the ModuleCat compositions and ideal-subtype inclusions before using the
    -- public evaluation API; their dependent section carriers prevent simp from matching.
    change (holomorphicStructureSheafModules.sectionsLinearEquiv I X V).symm
        ((holomorphicStructureSheaf I X).obj.map h f.1) x =
      (holomorphicStructureSheafModules I X).obj.map h
        ((holomorphicStructureSheafModules.sectionsLinearEquiv I X U).symm f.1) x
    simp only [holomorphicStructureSheafModules.sectionsLinearEquiv_symm_apply,
      holomorphicStructureSheafModules.map_apply, map_apply]

-- Supplying the model arguments explicitly lets simp use this lemma through opaque
-- dependent section carriers, as in simp only [vanishingSheafι_app_apply I X].
@[simp]
theorem vanishingSheafι_app_apply (D : X →₀ ℕ) (U : Opens X)
    (f : (vanishingSheaf I X D).obj.obj (op U)) (x : U) :
    (vanishingSheafι I X D).hom.app (op U) f x =
      (vanishingSheafSectionsEquiv I X D U f).1 x := by
  dsimp only [vanishingSheafι, ModuleCat.hom_ofHom, LinearMap.comp_apply,
    Submodule.subtype_apply, vanishingSheafSectionsEquiv, LinearEquiv.refl_apply]
  exact holomorphicStructureSheafModules.sectionsLinearEquiv_symm_apply I X (op U) f.1 x

/-- The inclusion is injective on sections. -/
theorem vanishingSheafι_app_injective (D : X →₀ ℕ) (U : Opens X) :
    Function.Injective ((vanishingSheafι I X D).hom.app (op U)) := by
  intro f g h
  apply (vanishingSheafSectionsEquiv I X D U).injective
  apply Subtype.ext
  apply holomorphicStructureSheaf.ext
  intro x
  have hx := congrArg (fun s ↦ s x) h
  rw [vanishingSheafι_app_apply, vanishingSheafι_app_apply] at hx
  exact hx

/-- The vanishing sheaf is a subobject of the holomorphic structure sheaf. -/
instance vanishingSheafι_mono (D : X →₀ ℕ) : Mono (vanishingSheafι I X D) := by
  have (U : (Opens X)ᵒᵖ) : Mono ((vanishingSheafι I X D).hom.app U) :=
    ConcreteCategory.mono_of_injective _ (vanishingSheafι_app_injective I X D U.unop)
  exact (sheafToPresheaf (Opens.grothendieckTopology X) (ModuleCat ℂ)).mono_of_mono_map
    (NatTrans.mono_of_mono_app (vanishingSheafι I X D).hom)

/-- Increasing the divisor induces an inclusion of vanishing sheaves in the reverse direction. -/
def vanishingSheafMapOfLE {D D' : X →₀ ℕ} (h : D ≤ D') :
    vanishingSheaf I X D' ⟶ vanishingSheaf I X D where
  hom.app U := ModuleCat.ofHom <| Submodule.inclusion
    (Submodule.restrictScalars_mono ℂ (vanishingIdeal_antitone I X U.unop h))
  hom.naturality := by
    intro U V f
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro s
    exact Subtype.ext rfl

/-- The inclusion between vanishing sheaves preserves the underlying holomorphic section. -/
@[simp]
theorem vanishingSheafMapOfLE_app {D D' : X →₀ ℕ} (h : D ≤ D') (U : Opens X)
    (f : (vanishingSheaf I X D').obj.obj (op U)) :
    (vanishingSheafSectionsEquiv I X D U
      ((vanishingSheafMapOfLE I X h).hom.app (op U) f)).1 =
        (vanishingSheafSectionsEquiv I X D' U f).1 := (rfl)

/-- The inclusion between vanishing sheaves commutes with inclusion into the structure sheaf. -/
@[reassoc (attr := simp), simp]
theorem vanishingSheafMapOfLE_ι {D D' : X →₀ ℕ} (h : D ≤ D') :
    vanishingSheafMapOfLE I X h ≫ vanishingSheafι I X D = vanishingSheafι I X D' := by
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro f
  rfl

/-- The map induced by increasing the divisor is a monomorphism. -/
instance vanishingSheafMapOfLE_mono {D D' : X →₀ ℕ} (h : D ≤ D') :
    Mono (vanishingSheafMapOfLE I X h) :=
  mono_of_mono_fac (vanishingSheafMapOfLE_ι I X h)

/-- Every allowed germ is represented by an allowed section on some neighborhood. -/
theorem exists_germ_eq_of_mem_pow_ker_eval [T1Space X] (D : X →₀ ℕ) (x : X)
    {g : (holomorphicStructureSheaf I X).presheaf.stalk x}
    (hg : g ∈ (RingHom.ker (eval I X x)) ^ D x) :
    ∃ (U : Opens X) (hx : x ∈ U) (f : vanishingIdeal I X D U),
      (holomorphicStructureSheaf I X).presheaf.germ U x hx f.1 = g := by
  classical
  obtain ⟨V, hxV, s, hs⟩ := (holomorphicStructureSheaf I X).presheaf.exists_germ_eq g
  let W : Opens X := ⟨(↑(D.support.erase x) : Set X)ᶜ,
    (D.support.erase x).finite_toSet.isClosed.isOpen_compl⟩
  have hxW : x ∈ W := by simp [W]
  let U := V ⊓ W
  have hxU : x ∈ U := ⟨hxV, hxW⟩
  let f := (holomorphicStructureSheaf I X).obj.map (homOfLE (inf_le_left : U ≤ V)).op s
  have hfg : (holomorphicStructureSheaf I X).presheaf.germ U x hxU f = g := by
    rw [TopCat.Presheaf.germ_res_apply]
    exact hs
  refine ⟨U, hxU, ⟨f, ?_⟩, hfg⟩
  rw [mem_vanishingIdeal]
  rintro ⟨y, hyU⟩
  by_cases hy : y = x
  · subst y
    rwa [hfg]
  · have hDy : D y = 0 := by
      have hny : y ∉ D.support.erase x := hyU.2
      simpa [Finset.mem_erase, hy, Finsupp.mem_support_iff] using hny
    simp [hDy]

/-- The prescribed stalk power consists exactly of germs of sections of the vanishing sheaf. -/
theorem mem_pow_ker_eval_iff_exists_germ [T1Space X] (D : X →₀ ℕ) (x : X)
    (g : (holomorphicStructureSheaf I X).presheaf.stalk x) :
    g ∈ (RingHom.ker (eval I X x)) ^ D x ↔
      ∃ (U : Opens X) (hx : x ∈ U) (f : vanishingIdeal I X D U),
        (holomorphicStructureSheaf I X).presheaf.germ U x hx f.1 = g := by
  constructor
  · exact exists_germ_eq_of_mem_pow_ker_eval I X D x
  · rintro ⟨U, hx, f, rfl⟩
    exact (mem_vanishingIdeal I X D U f.1).mp f.2 ⟨x, hx⟩

/-- On a compact connected complex manifold, a nonzero multiplicity function admits no nonzero
global holomorphic section with the prescribed vanishing. -/
theorem vanishingIdeal_top_eq_bot [I.Boundaryless] [IsManifold I 1 X]
    [CompactSpace X] [PreconnectedSpace X] (D : X →₀ ℕ) (hD : D ≠ 0) :
    vanishingIdeal I X D ⊤ = ⊥ := by
  classical
  apply eq_bot_iff.mpr
  intro f hf
  obtain ⟨x, hx⟩ : ∃ x, D x ≠ 0 := by
    by_contra h
    exact hD (Finsupp.ext fun x ↦ by simpa using not_exists.mp h x)
  have : Nonempty X := ⟨x⟩
  obtain ⟨c, rfl⟩ := (algebraMap_bijective I X).surjective f
  have hc := apply_eq_zero_of_mem_vanishingIdeal I X D ⊤ hf ⟨x, trivial⟩ hx
  simp only [algebraMap_apply] at hc
  simp [hc]

end TauCeti.holomorphicStructureSheaf
