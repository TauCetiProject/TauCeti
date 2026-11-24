/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.SimplicialComplex.Basic
public import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Finset.Union

/-!
# Basic abstract simplicial complex API

This file contains general-purpose lemmas supplementing Mathlib's basic abstract simplicial
complex API. The constructor `TauCeti.PreAbstractSimplicialComplex.ofGenerators` generates a
precomplex from a family of finite sets, and `TauCeti.AbstractSimplicialComplex.ofGenerators` is
the same construction for generators covering all vertices.

Faces are bundled by `TauCeti.SetLike.Face`, stated for an arbitrary set-like collection of
finite sets so that the same type describes the faces of an `AbstractSimplicialComplex` and of a
`PreAbstractSimplicialComplex`; hence its neutral namespace.
-/

public section

namespace TauCeti.SetLike

/-- A face of a set-like collection of finite sets, bundled with its membership proof. -/
abbrev Face {ι S : Type*} [_root_.SetLike S (Finset ι)] (K : S) := {σ : Finset ι // σ ∈ K}

/-- The order on bundled faces is inclusion of their underlying finite sets. -/
theorem face_le_iff {ι S : Type*} [_root_.SetLike S (Finset ι)] {K : S} {σ τ : Face K} :
    σ ≤ τ ↔ (σ : Finset ι) ⊆ τ :=
  Iff.rfl

end TauCeti.SetLike

namespace AbstractSimplicialComplex

/-- A finite set is a face of the underlying precomplex exactly when it is a face of the abstract
simplicial complex itself. This is the single place where the two `SetLike` instances are
identified. -/
@[simp]
theorem mem_toPreAbstractSimplicialComplex {ι : Type*} {K : AbstractSimplicialComplex ι}
    {σ : Finset ι} : σ ∈ K.toPreAbstractSimplicialComplex ↔ σ ∈ K :=
  Iff.rfl

end AbstractSimplicialComplex

namespace PreAbstractSimplicialComplex

variable {ι : Type*} {K L : PreAbstractSimplicialComplex ι} {σ : Finset ι} {v : ι}

/-- A finite set belongs to the underlying face set of a precomplex exactly when it is a face of
the precomplex. -/
theorem mem_faces : σ ∈ K.faces ↔ σ ∈ K :=
  Iff.rfl

/-- A face belongs to the image complex exactly when it is the image of a face of the source
complex. -/
theorem mem_map_iff {κ : Type*} [DecidableEq κ] {f : ι → κ}
    {τ : Finset κ} : τ ∈ K.map f ↔ ∃ σ, σ ∈ K ∧ σ.image f = τ :=
  Iff.rfl

/-- The face set of an image complex is the direct image of the source face set. -/
theorem faces_map {κ : Type*} [DecidableEq κ] (f : ι → κ) :
    (K.map f).faces = (fun σ : Finset ι => σ.image f) '' K.faces :=
  rfl

/-- Successive vertex maps agree with mapping by their composite. -/
@[simp]
theorem map_map {κ μ : Type*} [DecidableEq κ] [DecidableEq μ] (f : ι → κ) (g : κ → μ) :
    (K.map f).map g = K.map (g ∘ f) := by
  apply PreAbstractSimplicialComplex.ext
  simp only [faces_map, Set.image_image, Finset.image_image, Function.comp_def]

/-- The identity vertex map leaves a complex unchanged. -/
@[simp]
theorem map_id [DecidableEq ι] : K.map id = K := by
  refine SetLike.ext fun τ => ?_
  simp [mem_map_iff]

/-- Every precomplex with finitely many faces is supported on a finite set of ambient vertices. -/
theorem exists_finset_subset_of_finite_faces (hfin : K.faces.Finite) :
    ∃ V : Finset ι, ∀ σ ∈ K, σ ⊆ V := by
  classical
  exact ⟨hfin.toFinset.biUnion id, fun σ hσ _ hx =>
    Finset.mem_biUnion.mpr ⟨σ, hfin.mem_toFinset.mpr hσ, hx⟩⟩

/-- A finite set is a face of an intersection of two precomplexes exactly when it is a face of
both. -/
@[simp]
theorem mem_inf {ρ : Finset ι} : ρ ∈ K ⊓ L ↔ ρ ∈ K ∧ ρ ∈ L :=
  Iff.rfl

/-- Every vertex of a face spans a singleton face. -/
theorem singleton_mem_of_mem (hσ : σ ∈ K) (hv : v ∈ σ) : ({v} : Finset ι) ∈ K :=
  (K.isRelLowerSet_faces hσ).2 (Finset.singleton_subset_iff.mpr hv) (Finset.singleton_nonempty v)

/-- A vertex whose singleton is not a face occurs in no face at all.  This is the convenient way
to say that a vertex is *unused* by a complex, as needed when a construction adjoins a fresh
vertex. -/
theorem notMem_of_singleton_notMem (hv : ({v} : Finset ι) ∉ K) (hσ : σ ∈ K) : v ∉ σ :=
  fun h => hv (singleton_mem_of_mem hσ h)

/-- A relabeling injective on the vertices preserves and reflects finiteness of the face
collection. -/
theorem finite_faces_map_iff_of_injOn {κ : Type*} [DecidableEq κ]
    (f : ι → κ) (hf : Set.InjOn f {v | ({v} : Finset ι) ∈ K}) :
    (K.map f).faces.Finite ↔ K.faces.Finite := by
  rw [faces_map]
  refine Set.finite_image_iff fun σ hσ τ hτ hστ => ?_
  have hsub {ρ : Finset ι} (hρ : ρ ∈ K) : (ρ : Set ι) ⊆ {v | ({v} : Finset ι) ∈ K} :=
    fun _ hv => singleton_mem_of_mem hρ hv
  rw [← Finset.coe_inj, ← hf.image_eq_image_iff (hsub hσ) (hsub hτ), ← Finset.coe_image,
    ← Finset.coe_image, hστ]

/-- The image of a complex depends only on the values of the vertex map at its vertices. -/
theorem map_congr {κ : Type*} [DecidableEq κ] {f g : ι → κ}
    (h : ∀ x, ({x} : Finset ι) ∈ K → f x = g x) : K.map f = K.map g := by
  refine SetLike.ext fun τ => ?_
  simp only [mem_map_iff]
  refine exists_congr fun ρ => and_congr_right fun hρ => ?_
  rw [Finset.image_congr fun x hx => h x (singleton_mem_of_mem hρ hx)]

/-- The vertices of an image complex are the images of the vertices. -/
theorem singleton_mem_map_iff {κ : Type*} [DecidableEq κ] {f : ι → κ} {y : κ} :
    ({y} : Finset κ) ∈ K.map f ↔ ∃ x, ({x} : Finset ι) ∈ K ∧ f x = y := by
  constructor
  · intro h
    obtain ⟨ρ, hρ, hρy⟩ := mem_map_iff.mp h
    obtain ⟨x, hx⟩ := (K.isRelLowerSet_faces hρ).1
    have hfx : f x ∈ ρ.image f := Finset.mem_image_of_mem f hx
    rw [hρy, Finset.mem_singleton] at hfx
    exact ⟨x, singleton_mem_of_mem hρ hx, hfx⟩
  · rintro ⟨x, hx, rfl⟩
    exact mem_map_iff.mpr ⟨{x}, hx, Finset.image_singleton f x⟩

/-- Under an injective vertex map, the image of a finite set is a face of the image complex
exactly when the set is a face. -/
@[simp]
theorem image_mem_map_iff {κ : Type*} [DecidableEq κ] {f : ι → κ}
    (hf : Function.Injective f) : σ.image f ∈ K.map f ↔ σ ∈ K := by
  refine ⟨fun h => ?_, fun h => mem_map_iff.mpr ⟨σ, h, rfl⟩⟩
  obtain ⟨ρ, hρ, hρσ⟩ := mem_map_iff.mp h
  rwa [← Finset.image_injective hf hρσ]

/-- An injective vertex map is injective on complexes. -/
theorem map_injective {κ : Type*} [DecidableEq κ] {f : ι → κ} (hf : Function.Injective f) :
    Function.Injective fun K : PreAbstractSimplicialComplex ι => K.map f := by
  intro K L hKL
  refine SetLike.ext fun σ => ?_
  rw [← image_mem_map_iff (K := K) hf, ← image_mem_map_iff (K := L) hf]
  exact iff_of_eq (congrArg (σ.image f ∈ ·) hKL)

/-- The image of the void complex is void. -/
@[simp]
theorem map_bot {κ : Type*} [DecidableEq κ] (f : ι → κ) :
    (⊥ : PreAbstractSimplicialComplex ι).map f = ⊥ :=
  eq_bot_iff.mpr fun _ hτ => by
    obtain ⟨_, hρ, -⟩ := mem_map_iff.mp hτ
    exact hρ.elim

/-- Two pre-abstract simplicial complexes have the same image under an injective vertex map if and
only if they are equal. -/
theorem map_inj_of_injective {κ : Type*} [DecidableEq κ] (f : ι → κ)
    (hf : Function.Injective f) : K.map f = L.map f ↔ K = L :=
  (map_injective hf).eq_iff

/-- The image of a precomplex under any vertex map is void if and only if the source precomplex is
void. -/
@[simp]
theorem map_eq_bot_iff {κ : Type*} [DecidableEq κ] (f : ι → κ) :
    K.map f = ⊥ ↔ K = ⊥ := by
  constructor
  · intro h
    refine SetLike.ext fun σ => ⟨fun hσ => ?_, False.elim⟩
    have hmem : σ.image f ∈ K.map f := mem_map_iff.mpr ⟨σ, hσ, rfl⟩
    rw [h] at hmem
    exact hmem
  · rintro rfl
    exact map_bot f

/-- The finite set of all vertices occurring in faces of a finite-face precomplex. -/
noncomputable def faceUnion [DecidableEq ι] (hK : K.faces.Finite) : Finset ι :=
  hK.toFinset.biUnion id

/-- A vertex belongs to `faceUnion hK` if and only if its singleton is a face of `K`. -/
@[simp]
theorem mem_faceUnion [DecidableEq ι] (hK : K.faces.Finite) :
    v ∈ faceUnion hK ↔ ({v} : Finset ι) ∈ K := by
  simp only [faceUnion, Finset.mem_biUnion, Set.Finite.mem_toFinset, id_eq, mem_faces]
  exact ⟨fun ⟨σ, hσ, hv⟩ => singleton_mem_of_mem hσ hv,
    fun hv => ⟨{v}, hv, Finset.mem_singleton_self v⟩⟩

/-- Every face of a finite-face precomplex is contained in `faceUnion hK`. -/
theorem subset_faceUnion [DecidableEq ι] (hK : K.faces.Finite) (hσ : σ ∈ K) :
    σ ⊆ faceUnion hK :=
  Finset.subset_biUnion_of_mem id (hK.mem_toFinset.mpr hσ)

/-- `faceUnion hK` is contained in a finset `s` if and only if every face of `K` is contained
in `s`. -/
theorem faceUnion_subset_iff [DecidableEq ι] (hK : K.faces.Finite) {s : Finset ι} :
    faceUnion hK ⊆ s ↔ ∀ σ ∈ K, σ ⊆ s := by
  simp only [faceUnion, Finset.biUnion_subset, Set.Finite.mem_toFinset, id_eq, mem_faces]

/-- The vertex finset of a finite-face precomplex is empty if and only if the precomplex is
void. -/
@[simp]
theorem faceUnion_eq_empty_iff [DecidableEq ι] (hK : K.faces.Finite) :
    faceUnion hK = ∅ ↔ K = ⊥ := by
  rw [Finset.eq_empty_iff_forall_notMem, eq_bot_iff]
  refine ⟨fun h σ hσ => ?_, fun h v hv => h ((mem_faceUnion hK).mp hv)⟩
  obtain ⟨v, hv⟩ := (K.isRelLowerSet_faces hσ).1
  exact h v ((mem_faceUnion hK).mpr (singleton_mem_of_mem hσ hv))

/-- The vertex finset of the void precomplex is empty. -/
@[simp]
theorem faceUnion_bot [DecidableEq ι]
    (h : (⊥ : PreAbstractSimplicialComplex ι).faces.Finite) :
    faceUnion h = ∅ :=
  (faceUnion_eq_empty_iff h).mpr rfl

/-- `faceUnion` is monotone with respect to subcomplex inclusion. -/
theorem faceUnion_mono [DecidableEq ι] (hKL : K ≤ L)
    (hK : K.faces.Finite) (hL : L.faces.Finite) :
    faceUnion hK ⊆ faceUnion hL :=
  fun _ hv => (mem_faceUnion hL).mpr (hKL ((mem_faceUnion hK).mp hv))

/-- Mapping a finite-face precomplex along any vertex map images its vertex finset. -/
theorem faceUnion_map {κ : Type*} [DecidableEq ι] [DecidableEq κ] (f : ι → κ)
    (hK : K.faces.Finite) (hKf : (K.map f).faces.Finite) :
    faceUnion hKf = (faceUnion hK).image f := by
  ext y
  simp only [mem_faceUnion, singleton_mem_map_iff, Finset.mem_image]

end PreAbstractSimplicialComplex

namespace TauCeti.PreAbstractSimplicialComplex

/-- The precomplex generated by a family of finite sets: its faces are exactly the nonempty
subsets of the generators. The generators need not be maximal, and may be empty. -/
def ofGenerators {ι : Type*} (T : Set (Finset ι)) : _root_.PreAbstractSimplicialComplex ι where
  faces := {σ | σ.Nonempty ∧ ∃ t ∈ T, σ ⊆ t}
  isRelLowerSet_faces := by
    rintro σ ⟨hσ, t, ht, hσt⟩
    exact ⟨hσ, fun τ hτσ hτ => ⟨hτ, t, ht, hτσ.trans hσt⟩⟩

/-- Faces of a generated precomplex are precisely the nonempty subsets of its generators. -/
@[simp]
theorem mem_ofGenerators {ι : Type*} {T : Set (Finset ι)} {σ : Finset ι} :
    σ ∈ ofGenerators T ↔ σ.Nonempty ∧ ∃ t ∈ T, σ ⊆ t :=
  (Iff.rfl)

/-- Every nonempty generator is a face of the generated precomplex. -/
theorem mem_ofGenerators_of_mem {ι : Type*} {T : Set (Finset ι)} {t : Finset ι} (ht : t ∈ T)
    (hne : t.Nonempty) : t ∈ ofGenerators T :=
  mem_ofGenerators.mpr ⟨hne, t, ht, subset_rfl⟩

/-- A generated precomplex lies in a precomplex exactly when every nonempty generator is a
face. -/
@[simp]
theorem ofGenerators_le_iff {ι : Type*} {T : Set (Finset ι)}
    {K : _root_.PreAbstractSimplicialComplex ι} :
    ofGenerators T ≤ K ↔ ∀ t ∈ T, t.Nonempty → t ∈ K := by
  constructor
  · intro h t ht hne
    exact h (mem_ofGenerators_of_mem ht hne)
  · intro h σ hσ
    obtain ⟨hne, t, ht, hσt⟩ := mem_ofGenerators.mp hσ
    exact (K.isRelLowerSet_faces (h t ht (hne.mono hσt))).2 hσt hne

end TauCeti.PreAbstractSimplicialComplex

namespace TauCeti.AbstractSimplicialComplex

/-- The complex generated by a family of finite sets covering all vertices: the precomplex
`TauCeti.PreAbstractSimplicialComplex.ofGenerators T`, which contains every singleton. -/
def ofGenerators {ι : Type*} (T : Set (Finset ι)) (hcover : ∀ v, ∃ t ∈ T, v ∈ t) :
    _root_.AbstractSimplicialComplex ι :=
  _root_.PreAbstractSimplicialComplex.toAbstractSimplicialComplex ι
    (PreAbstractSimplicialComplex.ofGenerators T) fun v => by
    obtain ⟨t, ht, hv⟩ := hcover v
    exact ⟨Finset.singleton_nonempty v, t, ht, Finset.singleton_subset_iff.mpr hv⟩

/-- The underlying precomplex of a generated complex is the generated precomplex. -/
@[simp]
theorem toPreAbstractSimplicialComplex_ofGenerators {ι : Type*} {T : Set (Finset ι)}
    {hcover : ∀ v, ∃ t ∈ T, v ∈ t} :
    (ofGenerators T hcover).toPreAbstractSimplicialComplex =
      PreAbstractSimplicialComplex.ofGenerators T :=
  (rfl)

/-- Faces of a generated complex are precisely the nonempty subsets of its generators. -/
@[simp]
theorem mem_ofGenerators {ι : Type*} {T : Set (Finset ι)}
    {hcover : ∀ v, ∃ t ∈ T, v ∈ t} {σ : Finset ι} :
    σ ∈ ofGenerators T hcover ↔ σ.Nonempty ∧ ∃ t ∈ T, σ ⊆ t :=
  (Iff.rfl)

/-- Every nonempty generator is a face of the generated complex. -/
theorem mem_ofGenerators_of_mem {ι : Type*} {T : Set (Finset ι)}
    {hcover : ∀ v, ∃ t ∈ T, v ∈ t} {t : Finset ι} (ht : t ∈ T) (hne : t.Nonempty) :
    t ∈ ofGenerators T hcover :=
  mem_ofGenerators.mpr ⟨hne, t, ht, subset_rfl⟩

/-- A generated complex lies in a complex exactly when every nonempty generator is a face. -/
@[simp]
theorem ofGenerators_le_iff {ι : Type*} {T : Set (Finset ι)}
    {hcover : ∀ v, ∃ t ∈ T, v ∈ t} {K : _root_.AbstractSimplicialComplex ι} :
    ofGenerators T hcover ≤ K ↔ ∀ t ∈ T, t.Nonempty → t ∈ K :=
  PreAbstractSimplicialComplex.ofGenerators_le_iff (K := K.toPreAbstractSimplicialComplex)

/-- A finite set belongs to the full abstract simplicial complex exactly when it is nonempty. -/
theorem mem_top_iff {ι : Type*} {σ : Finset ι} :
    σ ∈ (⊤ : _root_.AbstractSimplicialComplex ι) ↔ σ.Nonempty :=
  Iff.rfl

/-- The faces of the bottom abstract complex are exactly the singletons. -/
@[simp]
theorem mem_bot {ι : Type*} {σ : Finset ι} :
    σ ∈ (⊥ : _root_.AbstractSimplicialComplex ι) ↔ ∃ v, σ = {v} :=
  Iff.rfl

end TauCeti.AbstractSimplicialComplex

namespace AbstractSimplicialComplex

/-- A complex is bottom if every face is a singleton face. -/
theorem eq_bot_of_surjective_singleton {ι : Type*} (K : AbstractSimplicialComplex ι)
    (h : Function.Surjective
      (fun i : ι => (⟨{i}, K.singleton_mem i⟩ : TauCeti.SetLike.Face K))) : K = ⊥ := by
  apply le_antisymm ?_ bot_le
  intro σ hσ
  obtain ⟨i, hi⟩ := h ⟨σ, hσ⟩
  exact TauCeti.AbstractSimplicialComplex.mem_bot.mpr
    ⟨i, (congrArg Subtype.val hi).symm⟩

end AbstractSimplicialComplex
