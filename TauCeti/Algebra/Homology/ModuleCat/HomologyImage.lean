/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.ModuleCat.Basic

/-!
# Homology classes represented in a submodule

Let `K` be a homological complex of modules and `V` a submodule of its degree-`n` term. The
homology classes of degree `n` that are represented by a cycle lying in `V` form a submodule of
the homology, `HomologicalComplex.moduleCatHomologyImage K n V`. When `V` is the degree-`n` term
of a subcomplex, these are the classes in the image of the homology of the subcomplex, since a
cycle of the subcomplex is exactly a cycle of `K` lying in it; the definition only needs the
single submodule `V`, not the subcomplex.

This is how a filtration of a complex by subcomplexes induces a filtration of its homology, the
setting of action-filtered Floer homology and its spectral invariants. The construction is
monotone in `V` and commutes with suprema of directed families of submodules, so a class
represented in an increasing union is represented at some stage. A chain map carrying `V` into
`W` carries the classes represented in `V` to classes represented in `W`.

## Main definitions

* `HomologicalComplex.moduleCatHomologyImage K n V`: the homology classes of degree `n`
  represented by a cycle lying in `V`.

## Main results

* `HomologicalComplex.mem_moduleCatHomologyImage_iff`: membership means having a representing
  cycle in `V`.
* `HomologicalComplex.moduleCatHomologyImage_iSup_of_directed`: the construction commutes with
  directed suprema.
* `HomologicalComplex.moduleCatHomologyImage_le_iSup_Iio`: the construction preserves left
  continuity of increasing families.
* `HomologicalComplex.map_moduleCatHomologyImage_le`: chain maps respect the construction.
-/

public section

open CategoryTheory

namespace HomologicalComplex

variable {R : Type*} [Ring R] {ι : Type*} {c : ComplexShape ι}
  (K : HomologicalComplex (ModuleCat R) c) (n : ι)

/-- The homology classes of degree `n` of a complex of modules that are represented by a cycle
lying in the submodule `V` of the degree-`n` term. When `V` is the degree-`n` term of a
subcomplex, these are the classes coming from the homology of the subcomplex. -/
noncomputable def moduleCatHomologyImage (V : Submodule R (K.X n)) : Submodule R (K.homology n) :=
  (V.comap (K.iCycles n).hom).map (K.homologyπ n).hom

variable {K n}

/-- A homology class lies in `K.moduleCatHomologyImage n V` exactly when it is represented by a
cycle lying in `V`. -/
theorem mem_moduleCatHomologyImage_iff {V : Submodule R (K.X n)} {σ : K.homology n} :
    σ ∈ K.moduleCatHomologyImage n V ↔
      ∃ z : K.cycles n, K.iCycles n z ∈ V ∧ K.homologyπ n z = σ :=
  Iff.rfl

/-- The class of a cycle lying in `V` is represented in `V`. -/
theorem homologyπ_mem_moduleCatHomologyImage {V : Submodule R (K.X n)} {z : K.cycles n}
    (hz : K.iCycles n z ∈ V) : K.homologyπ n z ∈ K.moduleCatHomologyImage n V :=
  ⟨z, hz, rfl⟩

variable (K n) in
/-- Classes represented in a smaller submodule are represented in a larger one. -/
theorem moduleCatHomologyImage_mono : Monotone (K.moduleCatHomologyImage n) :=
  fun _ _ h ↦ Submodule.map_mono (Submodule.comap_mono h)

variable (K n) in
/-- Only the zero class is represented in the zero submodule. -/
@[simp]
theorem moduleCatHomologyImage_bot : K.moduleCatHomologyImage n ⊥ = ⊥ := by
  refine eq_bot_iff.2 fun σ hσ ↦ ?_
  obtain ⟨z, hz, rfl⟩ := mem_moduleCatHomologyImage_iff.1 hσ
  rw [Submodule.mem_bot] at hz ⊢
  rw [moduleCat_iCycles_injective K n (hz.trans (map_zero _).symm), map_zero]

variable (K n) in
/-- Every homology class is represented in the whole term. -/
@[simp]
theorem moduleCatHomologyImage_top : K.moduleCatHomologyImage n ⊤ = ⊤ := by
  refine eq_top_iff.2 fun σ _ ↦ ?_
  obtain ⟨z, rfl⟩ := moduleCat_homologyπ_surjective K n σ
  exact homologyπ_mem_moduleCatHomologyImage Submodule.mem_top

/-- The classes represented in the supremum of a directed family of submodules are those
represented in one of its members: a representing cycle in the supremum already lies in one
member. -/
theorem moduleCatHomologyImage_iSup_of_directed {κ : Type*} (V : κ → Submodule R (K.X n))
    (hV : Directed (· ≤ ·) V) :
    K.moduleCatHomologyImage n (⨆ k, V k) = ⨆ k, K.moduleCatHomologyImage n (V k) := by
  refine le_antisymm ?_ (iSup_le fun k ↦ moduleCatHomologyImage_mono K n (le_iSup V k))
  rcases isEmpty_or_nonempty κ with hκ | hκ
  · simp
  intro σ hσ
  obtain ⟨z, hz, rfl⟩ := mem_moduleCatHomologyImage_iff.1 hσ
  obtain ⟨k, hk⟩ := (Submodule.mem_iSup_of_directed V hV).1 hz
  exact Submodule.mem_iSup_of_mem k (homologyπ_mem_moduleCatHomologyImage hk)

/-- A left continuous increasing family of submodules, each `F a` lying in the union of the
`F b` for `b < a`, induces a left continuous family of the classes they represent. -/
theorem moduleCatHomologyImage_le_iSup_Iio {α : Type*} [LinearOrder α]
    {F : α → Submodule R (K.X n)} (hF : Monotone F) {a : α} (h : F a ≤ ⨆ b : Set.Iio a, F b) :
    K.moduleCatHomologyImage n (F a) ≤ ⨆ b : Set.Iio a, K.moduleCatHomologyImage n (F b) :=
  (moduleCatHomologyImage_mono K n h).trans_eq
    (moduleCatHomologyImage_iSup_of_directed _ (hF.comp (Subtype.mono_coe _)).directed_le)

/-- A chain map carrying `V` into `W` in degree `n` carries the classes represented in `V` to
classes represented in `W`. -/
theorem map_moduleCatHomologyImage_le {L : HomologicalComplex (ModuleCat R) c} (φ : K ⟶ L)
    {V : Submodule R (K.X n)} {W : Submodule R (L.X n)} (h : V.map (φ.f n).hom ≤ W) :
    (K.moduleCatHomologyImage n V).map (homologyMap φ n).hom ≤ L.moduleCatHomologyImage n W := by
  rintro _ ⟨σ, hσ, rfl⟩
  obtain ⟨z, hz, rfl⟩ := mem_moduleCatHomologyImage_iff.1 hσ
  refine mem_moduleCatHomologyImage_iff.2
    ⟨cyclesMap φ n z, ?_, (moduleCat_homologyMap_homologyπ φ n z).symm⟩
  rw [moduleCat_iCycles_cyclesMap_apply]
  exact h ⟨_, hz, rfl⟩

end HomologicalComplex
