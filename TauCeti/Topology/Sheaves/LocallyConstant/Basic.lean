/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.CategoryTheory.Sites.LocallySurjective
public import Mathlib.Topology.LocallyConstant.Algebra
public import Mathlib.Topology.Sheaves.LocalPredicate
public import Mathlib.Topology.Sheaves.Forget

/-!
# The sheaf of locally constant functions

Let `X` be a topological space and `R` a ring. The locally constant `R`-valued functions on the
open subsets of `X` form a sheaf of rings `R_X`, the constant sheaf of rings with value `R`.
Its sections over a disconnected open are in general larger than `R`: on a discrete space with
two points the global sections are `R × R`.

The inclusion of constant functions is a morphism from the constant presheaf of rings with value
`R` to `R_X`. It is locally injective and locally surjective: two constants which agree on a
nonempty open are equal (on the empty open the empty family covers), and a locally constant
function is constant on each of its level sets, which are open. These are the hypotheses under
which Mathlib's `PresheafOfModules.sheafify` turns a sheaf of `R`-modules into a sheaf of
`R_X`-modules, which identifies sheaves of `R_X`-modules with sheaves of `R`-modules
(`TopCat.sheafModuleCatEquivSheafOfModules`).

## Main declarations

* `TopCat.locallyConstantLocal`: being locally constant is a local predicate on functions.
* `TopCat.locallyConstantPresheaf`, `TopCat.locallyConstantSheaf`: the presheaf and sheaf of rings
  `U ↦ LocallyConstant U R`.
* `TopCat.constToLocallyConstant`: the inclusion of constant functions, with instances saying
  that it is locally injective and locally surjective.
-/

@[expose] public section

universe u

open CategoryTheory Opposite TopologicalSpace

namespace TopCat

variable (X : TopCat.{u}) (R : Type u) [Ring R]

/-- Being locally constant is a local predicate on functions to a fixed type. -/
def locallyConstantLocal : LocalPredicate fun _ : X ↦ R where
  pred {_} f := IsLocallyConstant f
  res {_ _} i _ h := h.comp_continuous (Opens.isOpenEmbedding_of_le i.le).continuous
  locality {U} f w := by
    rw [IsLocallyConstant.iff_eventually_eq]
    intro x
    obtain ⟨V, hxV, i, hf⟩ := w x
    rw [IsLocallyConstant.iff_eventually_eq] at hf
    have h : ∀ᶠ y in Filter.map (Set.inclusion i.le) (nhds ⟨x, hxV⟩), f y = f x :=
      Filter.eventually_map.mpr ((hf ⟨x, hxV⟩).mono fun _ hy ↦ hy)
    rwa [(Opens.isOpenEmbedding_of_le i.le).map_nhds_eq] at h

/-- The presheaf of rings of locally constant `R`-valued functions, with restriction of
functions as restriction maps. -/
@[simps]
def locallyConstantPresheaf : (Opens X)ᵒᵖ ⥤ RingCat.{u} where
  obj U := RingCat.of (LocallyConstant U.unop R)
  map i := RingCat.ofHom (LocallyConstant.comapRingHom
    ⟨_, (Opens.isOpenEmbedding_of_le i.unop.le).continuous⟩)

/-- The presheaf of locally constant functions, read as sets, is the presheaf of functions
satisfying the local predicate `locallyConstantLocal`. -/
private def locallyConstantPresheafCompForgetIso :
    locallyConstantPresheaf X R ⋙ forget RingCat ≅
      subpresheafToTypes (locallyConstantLocal X R).toPrelocalPredicate :=
  NatIso.ofComponents (fun U ↦ Equiv.toIso
    ({ toFun f := ⟨f, f.isLocallyConstant⟩
       invFun f := ⟨f.1, f.2⟩ } :
      LocallyConstant U.unop R ≃ { f : U.unop → R // IsLocallyConstant f }))
    (fun _ ↦ rfl)

/-- Locally constant functions satisfy the sheaf condition. -/
theorem isSheaf_locallyConstantPresheaf :
    CategoryTheory.Presheaf.IsSheaf (Opens.grothendieckTopology X) (locallyConstantPresheaf X R) :=
  (Presheaf.isSheaf_iff_isSheaf_comp (forget RingCat) _).2 <|
    Presheaf.isSheaf_of_iso (locallyConstantPresheafCompForgetIso X R).symm
      (subpresheafToTypes.isSheaf _)

/-- The sheaf of rings `R_X` of locally constant `R`-valued functions on `X`. -/
def locallyConstantSheaf : CategoryTheory.Sheaf (Opens.grothendieckTopology X) RingCat.{u} :=
  ⟨locallyConstantPresheaf X R, isSheaf_locallyConstantPresheaf X R⟩

@[simp]
lemma locallyConstantSheaf_obj : (locallyConstantSheaf X R).obj = locallyConstantPresheaf X R :=
  rfl

/-- The inclusion of the constant presheaf of rings with value `R` into `R_X`, sending `r` to the
constant function with value `r`. -/
@[simps]
def constToLocallyConstant :
    (Functor.const (Opens X)ᵒᵖ).obj (RingCat.of R) ⟶ (locallyConstantSheaf X R).obj where
  app _ := RingCat.ofHom LocallyConstant.constRingHom

instance : Presheaf.IsLocallyInjective (Opens.grothendieckTopology X)
    (constToLocallyConstant X R) where
  equalizerSieve_mem {U} (r s : R) h := by
    rw [Opens.mem_grothendieckTopology]
    intro x hx
    have h' : LocallyConstant.const U.unop r = LocallyConstant.const U.unop s := h
    have : r = s := congr($h' ⟨x, hx⟩)
    exact ⟨_, 𝟙 _, by simp [Presheaf.equalizerSieve, this], hx⟩

instance : Presheaf.IsLocallySurjective (Opens.grothendieckTopology X)
    (constToLocallyConstant X R) where
  imageSieve_mem {U} (f : LocallyConstant U R) := by
    rw [Opens.mem_grothendieckTopology]
    intro x hx
    let W : Set U := f ⁻¹' {f ⟨x, hx⟩}
    have hW : IsOpen W := f.isLocallyConstant.isOpen_fiber _
    refine ⟨⟨Subtype.val '' W, U.isOpen.isOpenMap_subtype_val W hW⟩,
      homOfLE (by rintro _ ⟨y, -, rfl⟩; exact y.2), ⟨f ⟨x, hx⟩, ?_⟩, ⟨⟨x, hx⟩, rfl, rfl⟩⟩
    apply LocallyConstant.ext
    rintro ⟨_, y, hy, rfl⟩
    exact hy.symm

end TopCat
