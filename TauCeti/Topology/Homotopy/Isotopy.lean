/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Topology.Homotopy.Basic
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.Maps.Basic

/-!
# Isotopy and ambient isotopy

An *isotopy* between two continuous maps is a homotopy whose level-preserving total map
`I × X → I × Y` is a topological embedding, and an *ambient isotopy* of a space `Y` is a
homotopy from the identity of `Y` whose level-preserving total map `I × Y → I × Y` is a
homeomorphism. These are the point-set foundations that the geometric-topology roadmap
(`TauCetiRoadmap/GeometricTopology`) asks for once, in full generality, before specialising.
The definitions follow Burde--Zieschang, *Knots*, Chapter 1, Definitions 1.1 and 1.2,
generalized to this continuous topological setting. Later knot-equivalence foundations are
intended to specialize this continuous relation to smooth embeddings `S¹ ↪ M`; the same
notion also underlies locally flat isotopy, diffeotopies, and concordance.

## Main definitions

* `TauCeti.Isotopy f₀ f₁`: a homotopy from `f₀` to `f₁` whose total level-preserving map is a
  topological embedding.
* `TauCeti.Isotopic f₀ f₁`: the proposition that such an isotopy exists.
* `TauCeti.AmbientIsotopy Y`: a homotopy of `Y` from the identity whose total
  level-preserving map is a homeomorphism.

## Main results

* `TauCeti.Isotopy.isEmbedding_left` / `isEmbedding_right`: the endpoints of an isotopy are
  embeddings.
* `TauCeti.Isotopic.refl` / `TauCeti.Isotopic.symm`: isotopy is reflexive and symmetric.
* `TauCeti.Isotopic.homotopic`: isotopic maps are homotopic.
* `TauCeti.AmbientIsotopy.isotopic`: an ambient isotopy carries any embedding `f` to the
  isotopic embedding `Φ.final ∘ f`. This is the "ambient isotopy implies isotopy" direction.
-/

namespace TauCeti

open unitInterval ContinuousMap Topology

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

private theorem isEmbedding_const_prod (t : I) : IsEmbedding fun x : X => (t, x) :=
  IsEmbedding.of_comp (by fun_prop) continuous_snd (by
    convert (IsEmbedding.id : IsEmbedding (id : X → X)) using 1
    ext x
    rfl)

/-- An **isotopy** between `f₀ f₁ : C(X, Y)` is a homotopy whose level-preserving total map
`I × X → I × Y` is a topological embedding. -/
structure Isotopy (f₀ f₁ : C(X, Y)) extends Homotopy f₀ f₁ where
  /-- the level-preserving total map of an isotopy is a topological embedding -/
  isEmbedding_total' : IsEmbedding fun p : I × X => (p.1, toFun p)

namespace Isotopy

variable {f₀ f₁ : C(X, Y)}

instance instFunLike : FunLike (Isotopy f₀ f₁) (I × X) Y where
  coe F := F.toFun
  coe_injective
  | ⟨⟨⟨_, _⟩, _, _⟩, _⟩, ⟨⟨⟨_, _⟩, _, _⟩, _⟩, rfl => rfl

/-- The level-preserving total map of an isotopy. -/
def totalMap (F : Isotopy f₀ f₁) : C(I × X, I × Y) :=
  ⟨fun p => (p.1, F.toHomotopy p), by fun_prop⟩

@[simp]
theorem totalMap_apply (F : Isotopy f₀ f₁) (p : I × X) :
    F.totalMap p = (p.1, F.toHomotopy p) := rfl

/-- The level-preserving total map of an isotopy is a topological embedding. -/
theorem isEmbedding_total (F : Isotopy f₀ f₁) : IsEmbedding F.totalMap :=
  F.isEmbedding_total'

/-- Every time-slice of an isotopy is a topological embedding. -/
theorem isEmbedding_apply (F : Isotopy f₀ f₁) (t : I) :
    IsEmbedding fun x => F.toHomotopy (t, x) := by
  let k : Y → I × Y := fun y => (t, y)
  have hk_cont : Continuous k := by fun_prop
  have hcomp : IsEmbedding (k ∘ fun x => F.toHomotopy (t, x)) := by
    convert F.isEmbedding_total.comp (isEmbedding_const_prod (X := X) t) using 1
    ext x <;> rfl
  exact IsEmbedding.of_comp (by fun_prop) hk_cont hcomp

/-- An isotopy is, in particular, a `HomotopyWith` whose slices are embeddings. -/
def toHomotopyWith (F : Isotopy f₀ f₁) :
    HomotopyWith f₀ f₁ fun g : C(X, Y) => IsEmbedding g where
  toHomotopy := F.toHomotopy
  prop' := F.isEmbedding_apply

/-- The map an isotopy starts at is a topological embedding. -/
theorem isEmbedding_left (F : Isotopy f₀ f₁) : IsEmbedding f₀ := by
  simpa using F.isEmbedding_apply 0

/-- The map an isotopy ends at is a topological embedding. -/
theorem isEmbedding_right (F : Isotopy f₀ f₁) : IsEmbedding f₁ := by
  simpa using F.isEmbedding_apply 1

instance instHomotopyLike : HomotopyLike (Isotopy f₀ f₁) f₀ f₁ where
  map_continuous F := F.continuous_toFun
  map_zero_left F := F.map_zero_left
  map_one_left F := F.map_one_left

end Isotopy

/-- Two maps `f₀ f₁ : C(X, Y)` are **isotopic** if there is an isotopy between them. -/
def Isotopic (f₀ f₁ : C(X, Y)) : Prop :=
  Nonempty (Isotopy f₀ f₁)

namespace Isotopic

variable {f₀ f₁ : C(X, Y)}

/-- An isotopy witnesses that its endpoints are isotopic. -/
theorem of_isotopy (F : Isotopy f₀ f₁) : Isotopic f₀ f₁ := ⟨F⟩

/-- Isotopy is reflexive on embeddings. -/
theorem refl (f : C(X, Y)) (hf : IsEmbedding f) : Isotopic f f :=
  ⟨{ toHomotopy := Homotopy.refl f,
      isEmbedding_total' := IsEmbedding.id.prodMap hf }⟩

/-- Isotopy is symmetric. -/
@[symm]
theorem symm (h : Isotopic f₀ f₁) : Isotopic f₁ f₀ :=
  ⟨{ toHomotopy := h.some.toHomotopy.symm,
      isEmbedding_total' := by
        let e : I × X ≃ₜ I × X :=
          unitInterval.symmHomeomorph.prodCongr (Homeomorph.refl X)
        let e' : I × Y ≃ₜ I × Y :=
          unitInterval.symmHomeomorph.prodCongr (Homeomorph.refl Y)
        convert e'.isEmbedding.comp (h.some.isEmbedding_total.comp e.isEmbedding) using 1
        ext p
        · simp [Function.comp_def, Isotopy.totalMap, e, e', unitInterval.symm_symm]
        · exact congrArg h.some.toHomotopy (by ext <;> simp [e]) }⟩

/-- The endpoints of an isotopy relation are embeddings. -/
theorem isEmbedding_left (h : Isotopic f₀ f₁) : IsEmbedding f₀ :=
  Isotopy.isEmbedding_left h.some

/-- The right endpoint of an isotopy relation is an embedding. -/
theorem isEmbedding_right (h : Isotopic f₀ f₁) : IsEmbedding f₁ :=
  Isotopy.isEmbedding_right h.some

/-- Isotopic maps are homotopic. -/
theorem homotopic (h : Isotopic f₀ f₁) : Homotopic f₀ f₁ :=
  ⟨h.some.toHomotopy⟩

/-- Isotopic maps are homotopic through embeddings in Mathlib's generic API. -/
theorem homotopicWith (h : Isotopic f₀ f₁) :
    HomotopicWith f₀ f₁ fun g : C(X, Y) => IsEmbedding g :=
  ⟨h.some.toHomotopyWith⟩

end Isotopic

/-- An **ambient isotopy** of `Y` is a homotopy from the identity map of `Y` whose
level-preserving total map is a homeomorphism. The time-`1` map `Φ.final` is the resulting
homeomorphism. -/
structure AmbientIsotopy (Y : Type*) [TopologicalSpace Y] extends C(I × Y, Y) where
  /-- the level-preserving total map of the ambient isotopy is a homeomorphism -/
  isHomeomorph_total' : IsHomeomorph fun p : I × Y => (p.1, toFun p)
  /-- the ambient isotopy starts at the identity of `Y` -/
  map_zero_left' : ∀ y, toFun (0, y) = y

namespace AmbientIsotopy

variable (Φ : AmbientIsotopy Y)

/-- The level-preserving total map of an ambient isotopy. -/
def totalMap : C(I × Y, I × Y) :=
  ⟨fun p => (p.1, Φ.toContinuousMap p), by fun_prop⟩

@[simp]
theorem totalMap_apply (p : I × Y) : Φ.totalMap p = (p.1, Φ.toContinuousMap p) := rfl

/-- The level-preserving total map of an ambient isotopy is a homeomorphism. -/
theorem isHomeomorph_total : IsHomeomorph Φ.totalMap :=
  Φ.isHomeomorph_total'

/-- Every time-slice of an ambient isotopy is a self-homeomorphism of `Y`. -/
theorem isHomeomorph_apply (t : I) : IsHomeomorph fun y => Φ.toContinuousMap (t, y) := by
  rw [isHomeomorph_iff_isEmbedding_surjective]
  constructor
  · let k : Y → I × Y := fun y => (t, y)
    have hk_cont : Continuous k := by fun_prop
    have hcomp : IsEmbedding (k ∘ fun y => Φ.toContinuousMap (t, y)) := by
      convert Φ.isHomeomorph_total.isEmbedding.comp (isEmbedding_const_prod (X := Y) t) using 1
      ext y <;> rfl
    exact IsEmbedding.of_comp (by fun_prop) hk_cont hcomp
  · intro y
    rcases Φ.isHomeomorph_total.surjective (t, y) with ⟨p, hp⟩
    refine ⟨p.2, ?_⟩
    have ht : p.1 = t := congrArg Prod.fst hp
    rw [← ht]
    exact congrArg Prod.snd hp

/-- The ambient isotopy starts at the identity of `Y`. -/
theorem map_zero_left (y : Y) : Φ.toContinuousMap (0, y) = y :=
  Φ.map_zero_left' y

/-- The time-`1` homeomorphism produced by an ambient isotopy, as a continuous map. -/
def final : C(Y, Y) := ⟨fun y => Φ.toContinuousMap (1, y), by fun_prop⟩

@[simp]
theorem final_apply (y : Y) : Φ.final y = Φ.toContinuousMap (1, y) := rfl

/-- The final map produced by an ambient isotopy is a homeomorphism. -/
theorem isHomeomorph_final : IsHomeomorph Φ.final :=
  Φ.isHomeomorph_apply 1

/-- The time-`t` self-homeomorphism bundled as a `Homeomorph`. -/
noncomputable def homeomorph (t : I) : Y ≃ₜ Y :=
  IsHomeomorph.homeomorph (fun y => Φ.toContinuousMap (t, y)) (Φ.isHomeomorph_apply t)

@[simp]
theorem homeomorph_apply (t : I) (y : Y) : Φ.homeomorph t y = Φ.toContinuousMap (t, y) :=
  rfl

/-- The time-`1` homeomorphism produced by an ambient isotopy. -/
noncomputable def finalHomeomorph : Y ≃ₜ Y :=
  Φ.homeomorph 1

@[simp]
theorem finalHomeomorph_apply (y : Y) : Φ.finalHomeomorph y = Φ.final y :=
  rfl

/-- The constant ambient isotopy at the identity. -/
def refl (Y : Type*) [TopologicalSpace Y] : AmbientIsotopy Y where
  toContinuousMap := ⟨fun p => p.2, by fun_prop⟩
  isHomeomorph_total' := .id
  map_zero_left' _ := rfl

instance : Inhabited (AmbientIsotopy Y) := ⟨refl Y⟩

private theorem isotopy_totalMap_eq {f : C(X, Y)} :
    (fun p : I × X => (p.1, Φ.toContinuousMap (p.1, f p.2))) =
      Φ.totalMap ∘ Prod.map id f :=
  rfl

/-- An ambient isotopy carries any embedding `f` to the embedding `Φ.final ∘ f` through an
explicit isotopy: at time `t` the embedding is the homeomorphism `Φ t` postcomposed with `f`. -/
def isotopy {f : C(X, Y)} (hf : IsEmbedding f) : Isotopy f (Φ.final.comp f) where
  toHomotopy :=
    { toFun := fun p => Φ.toContinuousMap (p.1, f p.2)
      continuous_toFun := by fun_prop
      map_zero_left := fun x => Φ.map_zero_left (f x)
      map_one_left := fun _ => rfl }
  isEmbedding_total' := by
    rw [isotopy_totalMap_eq]
    exact Φ.isHomeomorph_total.isEmbedding.comp (IsEmbedding.id.prodMap hf)

/-- **Ambient isotopy implies isotopy**: an ambient isotopy of `Y` carries any embedding `f`
into `Y` to the isotopic embedding `Φ.final ∘ f`. -/
theorem isotopic {f : C(X, Y)} (hf : IsEmbedding f) : Isotopic f (Φ.final.comp f) :=
  ⟨Φ.isotopy hf⟩

end AmbientIsotopy

end TauCeti
