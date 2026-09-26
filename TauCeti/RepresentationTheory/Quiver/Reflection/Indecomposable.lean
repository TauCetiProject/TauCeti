/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import Mathlib.LinearAlgebra.Projection
public import TauCeti.CategoryTheory.Preadditive.Indecomposable
public import TauCeti.RepresentationTheory.Quiver.Reflection.Representation
public import TauCeti.RepresentationTheory.Quiver.Representation.Simple

/-!
# Reflecting an indecomposable representation at a sink

The Bernstein-Gelfand-Ponomarev reflection at a sink `i` replaces the vertex space `Mᵢ` by the
kernel of the sum `TauCeti.incomingSum` of the arrows into `i`, and it acts on dimension vectors by
the simple reflection `sᵢ` whenever that sum is onto (`TauCeti.dimVector_reflectRep`). This file
discharges that hypothesis: the sum of the arrows into a sink is onto for every indecomposable
representation except the vertex simple `Sᵢ`, which is the representation the reflection
annihilates.

One construction does the work. A linear endomorphism `π` of `Mᵢ` that the paths through `i` do
not see extends by the identity at the other vertices to an endomorphism `TauCeti.vertexEnd` of
the whole representation, idempotent as soon as `π` is. The category of representations is
abelian, hence idempotent complete, so an indecomposable object carries no idempotent endomorphism
besides `0` and the identity (`TauCeti.idempotent_eq_zero_or_id_of_indecomposable`), and therefore
`π` itself is `0` or the identity. Applied to the projection onto the range of the incoming sum
along a complement, this says the range is all of `Mᵢ` unless `M` vanishes away from `i`; applied
to the projection onto a line, it says a representation concentrated at `i` is a line there, hence
is `Sᵢ`, provided `i` carries no nontrivial closed path.

`TauCeti.vertexEnd` is stated at a vertex, not at a sink: naturality needs only that no path from
elsewhere into `i` sees `π` before it, that no path from `i` to elsewhere sees `π` after it, and
that `π` commutes with the maps of closed paths at `i`. At a sink the second condition is vacuous
and all closed paths are trivial; the dual construction at a source, in
`TauCeti.RepresentationTheory.Quiver.Reflection.Source.Indecomposable`, is the same theorem with
the first condition vacuous instead.

## Main definitions

* `TauCeti.vertexEnd`: the endomorphism of `M` acting by a given endomorphism of `Mᵢ` at a vertex
  `i` and by the identity elsewhere, with `TauCeti.vertexEnd_eq_id_iff` and
  `TauCeti.vertexEnd_eq_zero_iff` recognizing when it is trivial.

## Main results

* `TauCeti.vertexIdempotent_eq_id_or_eq_zero_of_indecomposable`: an idempotent of `Mᵢ` invisible to
  the paths through `i` is the identity, or is zero and `M` vanishes away from `i`, with
  `TauCeti.sinkIdempotent_eq_id_or_eq_zero_of_indecomposable` its form at a sink, where the
  hypothesis reads "`π` fixes the image of every arrow into `i`".
* `TauCeti.exists_ne_zero_span_eq_top_of_forall_subsingleton`,
  `TauCeti.dimVector_eq_single_of_forall_subsingleton` and
  `TauCeti.nonempty_iso_simpleRep_of_forall_subsingleton`: an indecomposable representation
  concentrated at a vertex with no nontrivial closed path is a line there, hence isomorphic to the
  vertex simple.
* `TauCeti.incomingSum_surjective_of_indecomposable`: **the sum of the arrows into a sink is onto
  for every indecomposable representation not isomorphic to the vertex simple there.**
* `TauCeti.dimVector_reflectRep_of_indecomposable`: consequently the reflection at a sink acts on
  the dimension vector of such a representation by the simple reflection at that vertex.

## Implementation notes

`TauCeti.sinkIdempotent_eq_id_or_eq_zero_of_indecomposable` takes its hypothesis on `π` in the form
"`π` fixes the image of each arrow into `i`" rather than "`π` fixes the range of
`TauCeti.incomingSum`". The two agree on a finite quiver, by
`TauCeti.map_toPath_mem_range_incomingSum`, but the arrow form needs no finiteness, and neither
then do the construction, its recognition lemmas, or the statement that an indecomposable
representation concentrated at a sink is a line there. Finiteness enters only where
`TauCeti.incomingSum` does.

The results comparing `M` with `TauCeti.simpleRep k Q i` are stated in the last section, where the
quiver, its arrows and the field all live in one universe. This is forced, not chosen: the vertex
spaces of a reflected representation are cut out of a product indexed by the arrows, so
`TauCeti.reflectRep` needs them in `max v w x`, while `Sᵢ` puts the field itself at `i` and so
needs them in the universe of the field. A statement mentioning both therefore has to identify the
two, and the general statements above -- which name no vertex simple -- are proved in the wider
setting and specialize to it.

As in the neighbouring files, a vertex `i : Q` is used as an object of the free category
`CategoryTheory.Paths Q`, which is `Q` only by unfolding a semireducible definition. Rewriting
cannot see through that identification, so every step that branches on equality of vertices is
factored through a lemma quantified over `Q`, and the components of `TauCeti.vertexEnd` are
supplied by the private `vertexEndApp`; `TauCeti.vertexEnd_app_self` and
`TauCeti.vertexEnd_app_of_ne` are the interface.

## References

This is the Layer 4 identity `dim (C⁺ᵢ M) = sᵢ · dim M` of
`TauCetiRoadmap/RepresentationTheory/QuiverRepresentations/README.md` with its hypothesis
discharged, and the input to the second milestone of that roadmap's Layer 5, that reflection
preserves indecomposability away from `Sᵢ`. See Bernstein--Gelfand--Ponomarev, *Coxeter functors
and Gabriel's theorem*, and Derksen--Weyman, *An Introduction to Quiver Representations*, Ch. 2.
-/

public section

namespace TauCeti

open CategoryTheory
open _root_.TauCeti.Quiver

universe u v w x

section General

variable {k : Type u} {Q : Type v} [Field k] [Quiver.{w} Q]
variable {M : QuiverRep.{u, v, w, max v w x} k Q} {i : Q}

/-! ### The endomorphism attached to an idempotent at a vertex -/

section VertexEnd

variable {π : M.obj i →ₗ[k] M.obj i}

variable (M π) in
open scoped Classical in
/-- The vertex components of `TauCeti.vertexEnd`: the given endomorphism at `i`, the identity
elsewhere. -/
private noncomputable def vertexEndApp (a : Q) : M.obj a ⟶ M.obj a :=
  if h : a = i then eqToHom (by rw [h]) ≫ ModuleCat.ofHom π ≫ eqToHom (by rw [h])
  else 𝟙 (M.obj a)

@[simp]
private theorem vertexEndApp_self : vertexEndApp M π i = ModuleCat.ofHom π := by
  classical
  simp only [vertexEndApp, dite_eq_left rfl, eqToHom_refl, Category.id_comp, Category.comp_id]

@[simp]
private theorem vertexEndApp_of_ne {a : Q} (ha : a ≠ i) : vertexEndApp M π a = 𝟙 (M.obj a) := by
  classical
  simp only [vertexEndApp, dite_eq_right ha]

/-- A vector fixed on the image of every arrow into `i` is fixed on the image of every path into
`i` from another vertex: such a path ends with an arrow into `i`. -/
private theorem map_path_fixed
    (hπ : ∀ (b : Q) (e : b ⟶ i) (z : M.obj b), π ((M.map e.toPath).hom z) =
      (M.map e.toPath).hom z)
    {a : Q} (ha : a ≠ i) (p : Quiver.Path a i) (y : M.obj a) :
    π ((M.map p).hom y) = (M.map p).hom y := by
  cases p with
  | nil => exact absurd rfl ha
  | cons q e =>
    have hcomp : M.map (q.cons e) = M.map q ≫ M.map e.toPath := M.map_comp q e.toPath
    rw [hcomp]
    exact hπ _ e _

private theorem vertexEndApp_naturality
    (hin : ∀ (a : Q) (p : Quiver.Path a i), a ≠ i → ∀ z : M.obj a,
      π ((M.map p).hom z) = (M.map p).hom z)
    (hout : ∀ (b : Q) (p : Quiver.Path i b), b ≠ i → ∀ y : M.obj i,
      (M.map p).hom (π y) = (M.map p).hom y)
    (hcomm : ∀ p : Quiver.Path i i,
      M.map p ≫ ModuleCat.ofHom π = ModuleCat.ofHom π ≫ M.map p)
    {a b : Q} (p : Quiver.Path a b) :
    M.map p ≫ vertexEndApp M π b = vertexEndApp M π a ≫ M.map p := by
  -- each `rcases` below substitutes the distinguished vertex away, so the four squares are read
  -- in the names the substitution leaves behind
  rcases eq_or_ne a i with rfl | ha
  · rcases eq_or_ne b a with rfl | hb
    · rw [vertexEndApp_self]
      exact hcomm p
    · rw [vertexEndApp_of_ne hb, vertexEndApp_self, Category.comp_id]
      exact ModuleCat.hom_ext (LinearMap.ext fun y ↦ (hout b p hb y).symm)
  · rw [vertexEndApp_of_ne ha, Category.id_comp]
    rcases eq_or_ne b i with rfl | hb
    · rw [vertexEndApp_self]
      exact ModuleCat.hom_ext (LinearMap.ext fun z ↦ hin a p ha z)
    · rw [vertexEndApp_of_ne hb, Category.comp_id]

variable (M) in
/-- **The endomorphism of `M` given by an endomorphism at one vertex.** For a linear endomorphism
`π` of `Mᵢ` that no path into `i` from elsewhere sees before it (`hin`), that no path out of `i`
to elsewhere sees after it (`hout`), and that commutes with every closed-path map at `i` (`hcomm`),
this is the endomorphism of `M` acting by `π` at `i` and by the identity at every other vertex.

The three hypotheses hold at a sink and, dually, at a source; they are what naturality asks for,
one case of the square for each of the four positions of `i` relative to the ends of a path. -/
noncomputable def vertexEnd (π : M.obj i →ₗ[k] M.obj i)
    (hin : ∀ (a : Q) (p : Quiver.Path a i), a ≠ i → ∀ z : M.obj a,
      π ((M.map p).hom z) = (M.map p).hom z)
    (hout : ∀ (b : Q) (p : Quiver.Path i b), b ≠ i → ∀ y : M.obj i,
      (M.map p).hom (π y) = (M.map p).hom y)
    (hcomm : ∀ p : Quiver.Path i i,
      M.map p ≫ ModuleCat.ofHom π = ModuleCat.ofHom π ≫ M.map p) : M ⟶ M where
  app a := vertexEndApp M π a
  naturality _ _ p := vertexEndApp_naturality hin hout hcomm p

variable
  {hin : ∀ (a : Q) (p : Quiver.Path a i), a ≠ i → ∀ z : M.obj a,
    π ((M.map p).hom z) = (M.map p).hom z}
  {hout : ∀ (b : Q) (p : Quiver.Path i b), b ≠ i → ∀ y : M.obj i,
    (M.map p).hom (π y) = (M.map p).hom y}
  {hcomm : ∀ p : Quiver.Path i i,
    M.map p ≫ ModuleCat.ofHom π = ModuleCat.ofHom π ≫ M.map p}

private theorem vertexEnd_app (a : Q) :
    (vertexEnd M π hin hout hcomm).app a = vertexEndApp M π a := rfl

/-- At its vertex, `TauCeti.vertexEnd` acts by the given endomorphism. -/
@[simp]
theorem vertexEnd_app_self : (vertexEnd M π hin hout hcomm).app i = ModuleCat.ofHom π :=
  (vertexEnd_app i).trans vertexEndApp_self

/-- Away from its vertex, `TauCeti.vertexEnd` acts by the identity. -/
@[simp]
theorem vertexEnd_app_of_ne {a : Q} (ha : a ≠ i) :
    (vertexEnd M π hin hout hcomm).app a = 𝟙 (M.obj a) :=
  (vertexEnd_app a).trans (vertexEndApp_of_ne ha)

private theorem vertexEndApp_comp_self (hidem : IsIdempotentElem π) (a : Q) :
    vertexEndApp M π a ≫ vertexEndApp M π a = vertexEndApp M π a := by
  rcases eq_or_ne a i with rfl | ha
  · rw [vertexEndApp_self, ← ModuleCat.ofHom_comp]
    exact congrArg ModuleCat.ofHom hidem
  · rw [vertexEndApp_of_ne ha, Category.comp_id]

private theorem vertexEndApp_eq_id (h : π = LinearMap.id) (a : Q) :
    vertexEndApp M π a = 𝟙 (M.obj a) := by
  rcases eq_or_ne a i with rfl | ha
  · rw [vertexEndApp_self, h]
    rfl
  · rw [vertexEndApp_of_ne ha]

private theorem vertexEndApp_eq_zero (hzero : π = 0)
    (hsub : ∀ a : Q, a ≠ i → Subsingleton (M.obj a)) (a : Q) : vertexEndApp M π a = 0 := by
  rcases eq_or_ne a i with rfl | ha
  · rw [vertexEndApp_self, hzero]
    rfl
  · have := hsub a ha
    rw [vertexEndApp_of_ne ha]
    exact (Limits.IsZero.iff_id_eq_zero _).mp (ModuleCat.isZero_of_subsingleton _)

/-- `TauCeti.vertexEnd` is idempotent as soon as the endomorphism it is built from is. -/
theorem vertexEnd_comp_self (hidem : IsIdempotentElem π) :
    vertexEnd M π hin hout hcomm ≫ vertexEnd M π hin hout hcomm = vertexEnd M π hin hout hcomm :=
  NatTrans.ext (funext fun a ↦ vertexEndApp_comp_self hidem a)

/-- `TauCeti.vertexEnd` is the identity exactly when the endomorphism it is built from is. -/
@[simp]
theorem vertexEnd_eq_id_iff : vertexEnd M π hin hout hcomm = 𝟙 M ↔ π = LinearMap.id := by
  refine ⟨fun h ↦ ?_, fun h ↦ NatTrans.ext (funext fun a ↦ vertexEndApp_eq_id h a)⟩
  have happ : (vertexEnd M π hin hout hcomm).app i = 𝟙 (M.obj i) := by rw [h]; rfl
  rw [vertexEnd_app_self] at happ
  exact congrArg ModuleCat.Hom.hom happ

/-- `TauCeti.vertexEnd` vanishes exactly when the endomorphism it is built from vanishes and the
representation is concentrated at its vertex: elsewhere it acts by the identity, which is zero only
on a vanishing vertex space. -/
@[simp]
theorem vertexEnd_eq_zero_iff :
    vertexEnd M π hin hout hcomm = 0 ↔ π = 0 ∧ ∀ a : Q, a ≠ i → Subsingleton (M.obj a) := by
  refine ⟨fun h ↦ ⟨?_, fun a ha ↦ ?_⟩,
    fun ⟨hzero, hsub⟩ ↦ NatTrans.ext (funext fun a ↦ vertexEndApp_eq_zero hzero hsub a)⟩
  · have happ : (vertexEnd M π hin hout hcomm).app i = 0 := by rw [h]; rfl
    rw [vertexEnd_app_self] at happ
    exact congrArg ModuleCat.Hom.hom happ
  · have happ : (vertexEnd M π hin hout hcomm).app a = 0 := by rw [h]; rfl
    rw [vertexEnd_app_of_ne ha] at happ
    exact ModuleCat.subsingleton_of_isZero ((Limits.IsZero.iff_id_eq_zero _).mpr happ)

end VertexEnd

/-! ### Idempotents at a vertex of an indecomposable representation -/

section Idempotents

private theorem isZero_of_forall_subsingleton (hall : ∀ a : Q, Subsingleton (M.obj a)) :
    Limits.IsZero M :=
  Functor.isZero _ fun a ↦ @ModuleCat.isZero_of_subsingleton k _ (M.obj a) (hall a)

/-- **An idempotent at a vertex of an indecomposable representation is trivial.** Let `M` be an
indecomposable representation. An idempotent endomorphism of `Mᵢ` invisible to the paths through
`i`, in the sense of
`TauCeti.vertexEnd`, is either the identity, or zero — and in the second case `M` vanishes away
from `i`. -/
theorem vertexIdempotent_eq_id_or_eq_zero_of_indecomposable
    (hM : Indecomposable M) (π : M.obj i →ₗ[k] M.obj i)
    (hin : ∀ (a : Q) (p : Quiver.Path a i), a ≠ i → ∀ z : M.obj a,
      π ((M.map p).hom z) = (M.map p).hom z)
    (hout : ∀ (b : Q) (p : Quiver.Path i b), b ≠ i → ∀ y : M.obj i,
      (M.map p).hom (π y) = (M.map p).hom y)
    (hcomm : ∀ p : Quiver.Path i i,
      M.map p ≫ ModuleCat.ofHom π = ModuleCat.ofHom π ≫ M.map p)
    (hidem : IsIdempotentElem π) :
    π = LinearMap.id ∨ π = 0 ∧ ∀ a : Q, a ≠ i → Subsingleton (M.obj a) := by
  rcases idempotent_eq_zero_or_id_of_indecomposable hM
      (vertexEnd_comp_self (hin := hin) (hout := hout) (hcomm := hcomm) hidem) with h | h
  · exact Or.inr ((vertexEnd_eq_zero_iff (hin := hin) (hout := hout) (hcomm := hcomm)).mp h)
  · exact Or.inl ((vertexEnd_eq_id_iff (hin := hin) (hout := hout) (hcomm := hcomm)).mp h)

/-- **An idempotent at a sink of an indecomposable representation is trivial.** Let `i` be a sink
of `Q` and `M` an indecomposable representation. An idempotent endomorphism of `Mᵢ` fixing the
image of every arrow into `i` is either the identity, or zero — and in the second case `M` vanishes
away from `i`. -/
theorem sinkIdempotent_eq_id_or_eq_zero_of_indecomposable (hi : IsSink i)
    (hM : Indecomposable M) (π : M.obj i →ₗ[k] M.obj i)
    (hπ : ∀ (b : Q) (e : b ⟶ i) (z : M.obj b), π ((M.map e.toPath).hom z) =
      (M.map e.toPath).hom z)
    (hidem : IsIdempotentElem π) :
    π = LinearMap.id ∨ π = 0 ∧ ∀ a : Q, a ≠ i → Subsingleton (M.obj a) :=
  vertexIdempotent_eq_id_or_eq_zero_of_indecomposable hM π
    (fun _ p ha z ↦ map_path_fixed hπ ha p z)
    (fun _ p hb ↦ absurd (hi.eq_of_path p).symm hb)
    (fun p ↦ by rw [hi.path_self_eq_nil p, QuiverRep.map_nil, Category.id_comp, Category.comp_id])
    hidem

/-- **An indecomposable representation concentrated at one vertex is a line there**: if `M`
vanishes away from a vertex `i` carrying no closed path but the trivial one, its vertex space at
`i` is spanned by a single nonzero vector. -/
theorem exists_ne_zero_span_eq_top_of_forall_subsingleton
    (hloop : ∀ p : Quiver.Path i i, p = Quiver.Path.nil)
    (hM : Indecomposable M) (h : ∀ a : Q, a ≠ i → Subsingleton (M.obj a)) :
    ∃ y : M.obj i, y ≠ 0 ∧ Submodule.span k {y} = ⊤ := by
  -- the vertex space at `i` is nonzero, since otherwise `M` would be a zero object
  have hnt : Nontrivial (M.obj i) := by
    rw [← not_subsingleton_iff_nontrivial]
    intro hs
    refine hM.1 (isZero_of_forall_subsingleton fun a ↦ ?_)
    rcases eq_or_ne a i with rfl | ha
    · exact hs
    · exact h a ha
  obtain ⟨y, hy⟩ := exists_ne (0 : M.obj i)
  refine ⟨y, hy, ?_⟩
  -- every path between `i` and another vertex has a vanishing end, so the projection onto the
  -- line through `y` extends to an endomorphism of `M`
  obtain ⟨U, hU⟩ := (Submodule.span k {y}).exists_isCompl
  have hidem : IsIdempotentElem ((Submodule.span k {y}).projection U hU) :=
    Submodule.isIdempotentElem_projection hU
  have hproj : LinearMap.IsProj (Submodule.span k {y})
      ((Submodule.span k {y}).projection U hU) := by
    have hrange := LinearMap.IsIdempotentElem.isProj_range _ hidem
    rwa [Submodule.range_projection hU] at hrange
  have hin : ∀ (a : Q) (p : Quiver.Path a i), a ≠ i → ∀ z : M.obj a,
      (Submodule.span k {y}).projection U hU ((M.map p).hom z) = (M.map p).hom z := by
    intro a p ha z
    have : Subsingleton (M.obj a) := h a ha
    rw [Subsingleton.elim z 0, map_zero, map_zero]
  have hout : ∀ (b : Q) (p : Quiver.Path i b), b ≠ i → ∀ z : M.obj i,
      (M.map p).hom ((Submodule.span k {y}).projection U hU z) = (M.map p).hom z := by
    intro b p hb z
    have : Subsingleton (M.obj b) := h b hb
    exact Subsingleton.elim _ _
  have hcomm : ∀ p : Quiver.Path i i,
      M.map p ≫ ModuleCat.ofHom ((Submodule.span k {y}).projection U hU) =
        ModuleCat.ofHom ((Submodule.span k {y}).projection U hU) ≫ M.map p := fun p ↦ by
    rw [hloop p, QuiverRep.map_nil, Category.id_comp, Category.comp_id]
  rcases vertexIdempotent_eq_id_or_eq_zero_of_indecomposable hM _ hin hout hcomm hidem with
    hid | ⟨hz, -⟩
  · exact hproj.submodule_eq_top_iff.mpr hid
  · -- the projection onto the line through `y` does not vanish
    exact absurd (Submodule.span_singleton_eq_bot.mp (hproj.submodule_eq_bot_iff.mpr hz)) hy

/-- **An indecomposable representation concentrated at a vertex carrying no nontrivial closed path
has the corresponding simple dimension vector.** -/
theorem dimVector_eq_single_of_forall_subsingleton [DecidableEq Q]
    (hloop : ∀ p : Quiver.Path i i, p = Quiver.Path.nil)
    (hM : Indecomposable M) (h : ∀ a : Q, a ≠ i → Subsingleton (M.obj a)) :
    (fun j : Q ↦ (dimVector M j : ℤ)) = Pi.single i 1 := by
  obtain ⟨y, hy, hspan⟩ := exists_ne_zero_span_eq_top_of_forall_subsingleton hloop hM h
  have hone : dimVector M i = 1 := by
    rw [dimVector_apply]
    exact (finrank_eq_one_iff_of_nonzero (K := k) y hy).mpr hspan
  have hzero : ∀ j : Q, j ≠ i → dimVector M j = 0 := by
    intro j hj
    let : Subsingleton (M.obj ((Paths.of Q).obj j)) := h j hj
    rw [dimVector_apply]
    exact Module.finrank_zero_of_subsingleton (R := k)
  funext j
  rcases eq_or_ne j i with rfl | hj
  · rw [Pi.single_eq_same, hone, Nat.cast_one]
  · rw [Pi.single_eq_of_ne hj, hzero j hj, Nat.cast_zero]

end Idempotents

/-! ### The surjectivity of the incoming sum -/

section IncomingSum

variable [Fintype Q] [∀ a b : Q, Fintype (a ⟶ b)]

/-- **The sum of the arrows into a sink of an indecomposable representation is onto, unless the
representation is concentrated at that sink.** This is the surjectivity hypothesis of
`TauCeti.dimVector_reflectRep`, discharged: the range of the incoming sum is a direct summand of
`Mᵢ`, so a proper range would split `M`, and the only splitting an indecomposable representation
admits leaves nothing outside the sink. -/
theorem incomingSum_surjective_or_forall_subsingleton (hi : IsSink i) (hM : Indecomposable M) :
    Function.Surjective (incomingSum M i) ∨ ∀ a : Q, a ≠ i → Subsingleton (M.obj a) := by
  -- project onto the range of the incoming sum along a complement
  obtain ⟨U, hU⟩ := (LinearMap.range (incomingSum M i)).exists_isCompl
  have hidem : IsIdempotentElem ((LinearMap.range (incomingSum M i)).projection U hU) :=
    Submodule.isIdempotentElem_projection hU
  have hproj : LinearMap.IsProj (LinearMap.range (incomingSum M i))
      ((LinearMap.range (incomingSum M i)).projection U hU) := by
    have hrange := LinearMap.IsIdempotentElem.isProj_range _ hidem
    rwa [Submodule.range_projection hU] at hrange
  have hπ : ∀ (b : Q) (e : b ⟶ i) (z : M.obj b),
      (LinearMap.range (incomingSum M i)).projection U hU ((M.map e.toPath).hom z) =
        (M.map e.toPath).hom z := fun b e z ↦
    (Submodule.projection_eq_self_iff hU _).mpr (map_toPath_mem_range_incomingSum M e z)
  rcases sinkIdempotent_eq_id_or_eq_zero_of_indecomposable hi hM _ hπ hidem with hid | ⟨-, hsub⟩
  · -- the projection onto the range is the identity, so the range is everything
    exact Or.inl (LinearMap.range_eq_top.mp (hproj.submodule_eq_top_iff.mpr hid))
  · exact Or.inr hsub

end IncomingSum

end General

/-! ### The vertex simple as the exceptional case -/

section VertexSimple

variable {k : Type u} {Q : Type u} [Field k] [Quiver.{u} Q]
variable {M : QuiverRep.{u, u, u, u} k Q} {i : Q}

/-- A representation concentrated at a vertex carrying no closed path but the trivial one is
annihilated by every path of positive length out of that vertex, so every vector of the vertex
space there satisfies the hypothesis of `TauCeti.simpleRepHom`. -/
private theorem map_eq_zero_of_forall_subsingleton
    (hloop : ∀ p : Quiver.Path i i, p = Quiver.Path.nil)
    (h : ∀ a : Q, a ≠ i → Subsingleton (M.obj a)) (y : M.obj ((Paths.of Q).obj i)) {a : Q}
    (p : Quiver.Path i a) (hp : p.length ≠ 0) : M.map p y = 0 := by
  rcases eq_or_ne a i with rfl | ha
  · rw [hloop p] at hp
    exact absurd Quiver.Path.length_nil hp
  · have := h a ha
    exact Subsingleton.elim _ _

/-- **An indecomposable representation concentrated at one vertex is the vertex simple there**,
provided that vertex carries no closed path but the trivial one. -/
theorem nonempty_iso_simpleRep_of_forall_subsingleton
    (hloop : ∀ p : Quiver.Path i i, p = Quiver.Path.nil) (hM : Indecomposable M)
    (h : ∀ a : Q, a ≠ i → Subsingleton (M.obj a)) : Nonempty (M ≅ simpleRep k Q i) := by
  obtain ⟨y, hy, hspan⟩ := exists_ne_zero_span_eq_top_of_forall_subsingleton hloop hM h
  have := isIso_simpleRepHom y (map_eq_zero_of_forall_subsingleton hloop h y) hy hspan fun a ha ↦
    @ModuleCat.isZero_of_subsingleton k _ (M.obj a) (h a ha)
  exact ⟨(asIso (simpleRepHom y (map_eq_zero_of_forall_subsingleton hloop h y))).symm⟩

variable [Fintype Q] [∀ a b : Q, Fintype (a ⟶ b)]

/-- **The sum of the arrows into a sink is onto for every indecomposable representation other than
the vertex simple there.** The vertex simple `Sᵢ` is genuinely excluded, by
`TauCeti.incomingSum_not_surjective`. -/
theorem incomingSum_surjective_of_indecomposable (hi : IsSink i) (hM : Indecomposable M)
    (hne : ¬ Nonempty (M ≅ simpleRep k Q i)) : Function.Surjective (incomingSum M i) :=
  (incomingSum_surjective_or_forall_subsingleton hi hM).resolve_right fun h ↦
    hne (nonempty_iso_simpleRep_of_forall_subsingleton hi.path_self_eq_nil hM h)

/-- **The reflection at a sink acts on the dimension vector of an indecomposable representation by
the simple reflection there**, unless that representation is the vertex simple at the sink, which
the reflection annihilates instead. This is the Layer 4 identity `dim (C⁺ᵢ M) = sᵢ · dim M` with
its hypothesis discharged. -/
theorem dimVector_reflectRep_of_indecomposable [DecidableEq Q] (hi : IsSink i)
    (hM : Indecomposable M) (hne : ¬ Nonempty (M ≅ simpleRep k Q i))
    (hfin : ∀ e : Σ b : Q, (b ⟶ i), FiniteDimensional k (M.obj e.1)) :
    (fun j : Q ↦ (dimVector (reflectRep M hi) j : ℤ))
      = vertexPreReflection Q i (fun j ↦ (dimVector M j : ℤ)) :=
  dimVector_reflectRep M hi hfin (incomingSum_surjective_of_indecomposable hi hM hne)

end VertexSimple

end TauCeti
