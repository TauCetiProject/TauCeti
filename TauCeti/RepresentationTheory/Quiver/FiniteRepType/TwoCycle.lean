/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Quiver.FiniteRepType.Embedding
import TauCeti.RepresentationTheory.Quiver.OneLoop.FiniteRepType

/-!
# Opposite arrows obstruct finite representation type

Two distinct vertices joined by arrows in both directions form an oriented two-cycle. Such a
quiver has infinite representation type over every field, including finite fields. This is the
cycle obstruction that the underlying simple graph cannot detect: that graph records a two-cycle
as a single edge.

Put the nilpotent Jordan block `k[X]/(Xⁿ⁺¹)` at both vertices, let the forward arrows act as the
identity, and let the reverse arrows act by multiplication by `X`. The identity arrow forces
an endomorphism to have equal components, and the reverse arrow forces that component to commute
with `X`. Thus its idempotents are exactly those of the existing one-loop Jordan block. These
representations are indecomposable and have distinct dimension vectors. Extension by zero then
gives the obstruction in any quiver containing opposite arrows.

## Main result

* `TauCeti.not_isFiniteRepType_of_opposite_hom`: opposite arrows between distinct vertices
  obstruct finite representation type.

## References

* I. Assem, D. Simson, A. Skowroński, *Elements of the Representation Theory of Associative
  Algebras*, Volume I, Chapter VII.

The construction uses `TauCeti.oneLoopNilpotentRep` and its indecomposability theorem; the
Jordan-block endomorphism calculation is reused rather than repeated.
-/

public section

namespace TauCeti

open CategoryTheory Polynomial

universe u v w

variable {k : Type u} [Field k] {Q : Type v} [_root_.Quiver.{w} Q]

/-- The two selected vertices, with all arrows inherited from the ambient quiver. -/
@[ext]
private structure TwoCycleVertex (x : Bool → Q) where
  idx : Bool

private instance (x : Bool → Q) : _root_.Quiver.{w} (TwoCycleVertex x) :=
  ⟨fun a b ↦ x a.idx ⟶ x b.idx⟩

private def twoCycleEmbedding {x : Bool → Q} (hx : Function.Injective x) :
    QuiverEmbedding (TwoCycleVertex x) Q where
  obj a := x a.idx
  map e := e
  obj_injective _ _ h := TwoCycleVertex.ext (hx h)
  map_injective := id

/-- The identity in the forward direction, the Jordan block in the reverse direction. -/
private noncomputable def twoCycleRep (x : Bool → Q) (n : ℕ) :
    QuiverRep.{u, 0, w, u} k (TwoCycleVertex x) :=
  Paths.lift
    { obj := fun _ ↦ ModuleCat.of k (AdjoinRoot ((X : k[X]) ^ (n + 1)))
      map := fun {a _} _ ↦ if a.idx then
        ModuleCat.ofHom (LinearMap.mulLeft k (AdjoinRoot.root ((X : k[X]) ^ (n + 1))))
        else 𝟙 _ }

private theorem twoCycleRep_map {x : Bool → Q} {n : ℕ} {a b : TwoCycleVertex x} (e : a ⟶ b) :
    (twoCycleRep (k := k) x n).map (_root_.Quiver.Hom.toPath e) =
      if a.idx then
        ModuleCat.ofHom (LinearMap.mulLeft k (AdjoinRoot.root ((X : k[X]) ^ (n + 1))))
      else 𝟙 _ :=
  Paths.lift_toPath _ _

variable {x : Bool → Q} {n : ℕ}
variable (α : x false ⟶ x true) (β : x true ⟶ x false)

include α in
/-- The forward identity arrow forces the two components of an endomorphism to agree. -/
private theorem twoCycleRep_app_eq (f : twoCycleRep (k := k) x n ⟶ twoCycleRep x n)
    (a : TwoCycleVertex x) : f.app a = f.app (⟨false⟩ : TwoCycleVertex x) := by
  have h := f.naturality (_root_.Quiver.Hom.toPath
    (α : (⟨false⟩ : TwoCycleVertex x) ⟶ ⟨true⟩))
  simp only [twoCycleRep_map, Bool.false_eq_true, ↓reduceIte] at h
  rcases a with ⟨_ | _⟩
  · rfl
  · exact h

/-- Read the common component as an endomorphism of the existing one-loop Jordan block. -/
private noncomputable def twoCycleLoopEnd (α : x false ⟶ x true) (β : x true ⟶ x false)
    (f : twoCycleRep (k := k) x n ⟶ twoCycleRep x n) :
    oneLoopNilpotentRep.{u, w} k n ⟶ oneLoopNilpotentRep.{u, w} k n :=
  Paths.liftNatTrans (fun _ ↦ f.app (⟨false⟩ : TwoCycleVertex x)) (fun {a b} e ↦ by
    cases a
    cases b
    have h := f.naturality (_root_.Quiver.Hom.toPath
      (β : (⟨true⟩ : TwoCycleVertex x) ⟶ ⟨false⟩))
    rw [twoCycleRep_map, twoCycleRep_app_eq α f ⟨true⟩] at h
    -- Both vertex spaces are the same truncated polynomial algebra, so this is
    -- precisely the one-loop naturality square.
    rw [Subsingleton.elim e Quiver.OneLoop.loop, oneLoopNilpotentRep_map_loop]
    exact h)

private theorem twoCycleLoopEnd_app (f : twoCycleRep (k := k) x n ⟶ twoCycleRep x n)
    (a : Paths Quiver.OneLoop) :
    (twoCycleLoopEnd α β f).app a = f.app (⟨false⟩ : TwoCycleVertex x) := (rfl)

/-- An endomorphism is determined by its common component. -/
private theorem twoCycleLoopEnd_injective :
    Function.Injective (twoCycleLoopEnd (k := k) (n := n) α β) := by
  intro f g h
  have h0 := congrArg (fun η ↦ η.app (Quiver.OneLoop.vertex : Paths Quiver.OneLoop)) h
  rw [twoCycleLoopEnd_app α β f Quiver.OneLoop.vertex,
    twoCycleLoopEnd_app α β g Quiver.OneLoop.vertex] at h0
  exact NatTrans.ext (funext fun a ↦ by
    rw [twoCycleRep_app_eq α f a, twoCycleRep_app_eq α g a, h0])

include α β in
private theorem indecomposable_twoCycleRep : Indecomposable (twoCycleRep (k := k) x n) := by
  have hnz : ¬ Limits.IsZero (twoCycleRep (k := k) x n) := fun h ↦ by
    have : Subsingleton (AdjoinRoot ((X : k[X]) ^ (n + 1))) :=
      ModuleCat.subsingleton_of_isZero (h.obj ((⟨false⟩ : TwoCycleVertex x) : Paths _))
    exact false_of_nontrivial_of_subsingleton (AdjoinRoot ((X : k[X]) ^ (n + 1)))
  refine indecomposable_of_idempotent_eq_zero_or_id hnz fun f hf ↦ ?_
  have hidem : twoCycleLoopEnd α β f ≫ twoCycleLoopEnd α β f = twoCycleLoopEnd α β f := by
    apply NatTrans.ext
    funext a
    rw [NatTrans.comp_app, twoCycleLoopEnd_app]
    exact congrArg (fun η ↦ η.app (⟨false⟩ : TwoCycleVertex x)) hf
  rcases idempotent_eq_zero_or_id_of_indecomposable (indecomposable_oneLoopNilpotentRep n)
      hidem with h0 | h1
  · exact Or.inl (twoCycleLoopEnd_injective α β (h0.trans (by ext; rfl)))
  · exact Or.inr (twoCycleLoopEnd_injective α β (h1.trans (by ext; rfl)))

private theorem dimVector_twoCycleRep (a : TwoCycleVertex x) :
    dimVector (twoCycleRep (k := k) x n) a = n + 1 := by
  rw [dimVector_apply]
  -- The vertex space is the same quotient as in the one-loop block.
  exact finrank_quotient_span_eq_natDegree.trans (natDegree_X_pow (n + 1))

include α β in
private theorem not_isFiniteRepType_twoCycleVertex :
    ¬ IsFiniteRepType.{u, 0, w, u} k (TwoCycleVertex x) :=
  not_isFiniteRepType_of_infinite (M := twoCycleRep (k := k) x)
    (fun n ↦ isFinDim_iff.mpr fun _ ↦ (monic_X_pow (R := k) (n + 1)).finite_adjoinRoot)
    (fun _ ↦ indecomposable_twoCycleRep α β) fun r s hrs ⟨e⟩ ↦ hrs <| by
      have h := congrFun (dimVector_eq_of_iso e) ⟨false⟩
      rw [dimVector_twoCycleRep, dimVector_twoCycleRep] at h
      omega

/-- Opposite arrows between distinct vertices obstruct finite representation type over every
field. No finiteness assumption on the ambient quiver is needed. -/
theorem not_isFiniteRepType_of_opposite_hom {a b : Q} (hab : a ≠ b)
    (α : a ⟶ b) (β : b ⟶ a) : ¬ IsFiniteRepType.{u, v, w, u} k Q := by
  let x : Bool → Q := fun t ↦ if t then b else a
  have hx : Function.Injective x := by
    intro i j hij
    cases i <;> cases j <;> simp_all [x]
  exact fun h ↦ not_isFiniteRepType_twoCycleVertex (x := x) α β
    (h.of_quiverEmbedding (twoCycleEmbedding hx))

end TauCeti
