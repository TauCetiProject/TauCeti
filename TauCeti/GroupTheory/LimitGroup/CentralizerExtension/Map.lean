/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.LimitGroup.CentralizerExtension.Basic
public import TauCeti.GroupTheory.PushoutI.Map
import TauCeti.GroupTheory.Subgroup.Centralizer

/-!
# Extensions of centralizers along an embedding of the base group

A homomorphism `f : G →* K` maps the centralizer of `u` into the centralizer of `f u`, so it
induces a homomorphism `G(u, ℤⁿ) →* K(f u, ℤⁿ)` of the extensions of centralizers, the identity on
the new letters. If `f` is injective, so is the induced homomorphism: `f` identifies `C_G(u)` with
`f(G) ∩ C_K(f u)`, so reduced words of the amalgam `G(u, ℤⁿ)` are sent to reduced words of
`K(f u, ℤⁿ)`. No hypothesis on `G`, `K`, `u` or `n` is needed; in particular `C_K(f u)` may be
larger than `f(C_G(u))`.

## Main definitions

* `TauCeti.LimitGroup.CentralizerExt.map`: the homomorphism `G(u, ℤⁿ) →* K(f u, ℤⁿ)` induced by
  `f : G →* K`.

## Main results

* `TauCeti.LimitGroup.CentralizerExt.map_injective`: it is injective if `f` is, an instance of the
  injectivity criterion `Monoid.PushoutI.map_injective` for homomorphisms of amalgamated products.
* `TauCeti.LimitGroup.CentralizerExt.map_injective_iff`: it is injective exactly when `f` is.

## References

* O. Kharlampovich, A. Myasnikov, *Implicit function theorem over free groups*, J. Algebra 290
  (2005), §2.5.
* A. Myasnikov, V. Remeslennikov, *Exponential groups 2: extensions of centralizers and tensor
  completion of CSA-groups*, Internat. J. Algebra Comput. 6 (1996), §4.
-/

public section

open Subgroup

namespace TauCeti.LimitGroup

namespace CentralizerExt

variable {G K : Type*} [Group G] [Group K]

/-- The homomorphism `G(u, ℤⁿ) →* K(f u, ℤⁿ)` induced by `f : G →* K`: it is `f` on `G` and the
identity on the new letters. -/
def map (f : G →* K) (u : G) (n : ℕ) : CentralizerExt u n →* CentralizerExt (f u) n :=
  -- Naming `f c` spares the elaborator a costly unification of `(of.comp f) c` with `of ?c`.
  lift (of.comp f) t commute_t_t fun c hc => commute_of_t (c := f c) <| by
    simpa using (f.centralizerMap Set.image_singleton.superset ⟨c, hc⟩).2

@[simp]
theorem map_of (f : G →* K) (u : G) (n : ℕ) (g : G) : map f u n (of g) = of (f g) :=
  lift_of _ _ _ _ g

@[simp]
theorem map_t (f : G →* K) (u : G) (n : ℕ) (i : Fin n) : map f u n (t i) = t i :=
  lift_t _ _ _ _ i

@[simp]
theorem map_comp_of (f : G →* K) (u : G) (n : ℕ) : (map f u n).comp of = of.comp f :=
  lift_comp_of _ _ _ _

@[simp]
theorem map_id (u : G) (n : ℕ) : map (.id G) u n = .id (CentralizerExt u n) :=
  hom_ext (MonoidHom.ext (map_of _ u n)) (map_t _ u n)

theorem map_comp {L : Type*} [Group L] (g : K →* L) (f : G →* K) (u : G) (n : ℕ) :
    map (g.comp f) u n = (map g (f u) n).comp (map f u n) :=
  hom_ext (by ext; simp) (by simp)

/-- The homomorphisms induced by `f : G →* K` on the two factors of the amalgam `G(u, ℤⁿ)`: `f`
itself on `G`, and its restriction to the centralizers times the identity on `C_G(u) × ℤⁿ`. -/
private def factorMap (f : G →* K) (u : G) (n : ℕ) :
    ∀ b, CentralizerExtFactor u n b →* CentralizerExtFactor (f u) n b
  | false => f
  | true => (f.centralizerMap Set.image_singleton.superset).prodMap (.id _)

private theorem factorMap_comp (f : G →* K) (u : G) (n : ℕ) (b : Bool) :
    (factorMap f u n b).comp (centralizerExtMap u n b) =
      (centralizerExtMap (f u) n b).comp (f.centralizerMap Set.image_singleton.superset) := by
  cases b
  · ext
    simp [factorMap]
  · -- Unfolding `factorMap`, `MonoidHom.prodMap` and `MonoidHom.inl`, both sides are
    -- `c ↦ (f.centralizerMap _ c, 1)`.
    rw [centralizerExtMap_true, centralizerExtMap_true]
    rfl

/-- The induced homomorphism of extensions of centralizers, as a homomorphism of amalgamated
products induced by homomorphisms of the factors. -/
private theorem map_eq_pushoutIMap (f : G →* K) (u : G) (n : ℕ) :
    map f u n =
      Monoid.PushoutI.map (factorMap f u n) (f.centralizerMap Set.image_singleton.superset)
        (factorMap_comp f u n) := by
  refine hom_ext (MonoidHom.ext fun g => ?_) fun i => ?_
  · simpa [of_def, factorMap] using map_of f u n g
  · rw [map_t, t_def, t_def, Monoid.PushoutI.map_of]
    -- On the second factor the homomorphism is `(c, v) ↦ (f c, v)`, and `f 1 = 1`.
    exact congrArg _ (Prod.ext (map_one (f.centralizerMap _)).symm rfl)

/-- The homomorphism of extensions of centralizers induced by an injective homomorphism is
injective. -/
theorem map_injective {f : G →* K} (hf : Function.Injective f) (u : G) (n : ℕ) :
    Function.Injective (map f u n) := by
  rw [map_eq_pushoutIMap]
  refine Monoid.PushoutI.map_injective _ (centralizerExtMap_injective (f u) n)
    (MonoidHom.centralizerMap_injective hf _) fun b => ?_
  cases b
  · -- An element of `G` whose image centralizes `f u` centralizes `u`.
    rintro (g : G) ⟨c, hc⟩
    rw [centralizerExtMap_false] at hc ⊢
    refine ⟨⟨g, mem_centralizer_singleton_iff.2 (hf ?_)⟩, rfl⟩
    -- `hc` says `c = f g`: `factorMap f u n false` is `f` by definition.
    rw [map_mul, map_mul, ← show (c : K) = f g from hc, mem_centralizer_singleton_iff.1 c.2]
  · -- A letter `(c, v)` of `C_G(u) × ℤⁿ` whose image lies in `C_K(f u) × 1` has `v = 1`.
    rintro ⟨c, v⟩ ⟨c', hc'⟩
    rw [centralizerExtMap_true] at hc' ⊢
    have hv : (1 : Fin n → Multiplicative ℤ) = v := congrArg Prod.snd hc'
    exact ⟨c, Prod.ext rfl hv⟩

/-- The homomorphism of extensions of centralizers induced by `f` is injective exactly when `f`
is. -/
theorem map_injective_iff {f : G →* K} (u : G) (n : ℕ) :
    Function.Injective (map f u n) ↔ Function.Injective f := by
  refine ⟨fun h => ?_, fun hf => map_injective hf u n⟩
  rw [← (of_injective (u := f u) (n := n)).of_comp_iff, ← MonoidHom.coe_comp, ← map_comp_of]
  exact h.comp of_injective

end CentralizerExt

end TauCeti.LimitGroup
