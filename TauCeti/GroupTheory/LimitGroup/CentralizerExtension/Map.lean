/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.LimitGroup.CentralizerExtension.Basic
public import TauCeti.GroupTheory.PushoutI.Map
import Mathlib.Order.Filter.Map
import TauCeti.GroupTheory.Subgroup.Centralizer

/-!
# Extensions of centralizers along an embedding of the base group

A homomorphism `f : G →* K` maps the centralizer of `u` into the centralizer of `f u`, so it
induces a homomorphism `G(u, ℤⁿ) →* K(f u, ℤⁿ)` of the extensions of centralizers, the identity on
the new letters. If homomorphisms `fᵢ` eventually keep every nonidentity element of `G` along a
filter, the induced homomorphisms eventually keep every nonidentity element of `G(u, ℤⁿ)`: a letter
`g ∉ C_G(u)` is eventually mapped outside `C_{Kᵢ}(fᵢ u)`, since eventually `fᵢ [g, u] ≠ 1`, so
reduced words of the amalgam `G(u, ℤⁿ)` are eventually sent to reduced words. In particular, if
`f` is injective, so is the induced homomorphism. No hypothesis on `G`, `K`, `u` or `n` is needed;
in particular `C_K(f u)` may be larger than `f(C_G(u))`.

## Main definitions

* `TauCeti.LimitGroup.CentralizerExt.map`: the homomorphism `G(u, ℤⁿ) →* K(f u, ℤⁿ)` induced by
  `f : G →* K`.

## Main results

* `TauCeti.LimitGroup.CentralizerExt.eventually_map_ne_one`: if homomorphisms `fᵢ` (to possibly
  different groups) eventually keep every nonidentity element of `G` along a filter, the induced
  homomorphisms eventually keep every nonidentity element of `G(u, ℤⁿ)`, an instance of the
  criterion `Monoid.PushoutI.eventually_map_ne_one` for homomorphisms of amalgamated products.
* `TauCeti.LimitGroup.CentralizerExt.map_injective`: it is injective if `f` is.
* `TauCeti.LimitGroup.CentralizerExt.map_injective_iff`: it is injective exactly when `f` is.

## References

* O. Kharlampovich, A. Myasnikov, *Implicit function theorem over free groups*, J. Algebra 290
  (2005), §2.5.
* A. Myasnikov, V. Remeslennikov, *Exponential groups 2: extensions of centralizers and tensor
  completion of CSA-groups*, Internat. J. Algebra Comput. 6 (1996), §4.
-/

public section

open Subgroup
open scoped commutatorElement

namespace TauCeti.LimitGroup

namespace CentralizerExt

variable {G K : Type*} [Group G] [Group K]

/-- The homomorphism `G(u, ℤⁿ) →* K(f u, ℤⁿ)` induced by `f : G →* K`: it is `f` on `G` and the
identity on the new letters. -/
def map (f : G →* K) (u : G) (n : ℕ) : CentralizerExt u n →* CentralizerExt (f u) n :=
  -- Naming `f c` spares the elaborator a costly unification of `(of.comp f) c` with `of ?c`.
  lift (of.comp f) t commute_t_t fun c hc => commute_of_t (c := f c) <| by
    simpa using (f.centralizerMap Set.image_singleton.superset ⟨c, hc⟩).property

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

/-- If homomorphisms `fᵢ` eventually keep every nonidentity element of `G`, a letter of `G(u, ℤⁿ)`
outside `C_G(u)` eventually has its image outside `C_{Kᵢ}(fᵢ u)`: a letter `g ∉ C_G(u)` once
`fᵢ [g, u] ≠ 1`, and a letter `(c, v)` with `v ≠ 0` always. -/
private theorem eventually_factorMap_notMem_range {ι : Type*} {l : Filter ι} {K : ι → Type*}
    [∀ i, Group (K i)] {f : ∀ i, G →* K i} (hf : ∀ g : G, g ≠ 1 → ∀ᶠ i in l, f i g ≠ 1) (u : G)
    (n : ℕ) (b : Bool) {g : CentralizerExtFactor u n b} (hg : g ∉ (centralizerExtMap u n b).range) :
    ∀ᶠ i in l, factorMap (f i) u n b g ∉ (centralizerExtMap (f i u) n b).range := by
  cases b
  · -- The factor `CentralizerExtFactor u n false` unfolds to `G`, but without the ascription the
    -- commutator elaborates to an instance problem `Bracket (CentralizerExtFactor u n false) G`
    -- that instance search does not solve.
    have hg' : ⁅(show G from g), u⁆ ≠ 1 := by
      simpa [commutatorElement_eq_one_iff_commute, mem_centralizer_singleton_iff] using hg
    filter_upwards [hf _ hg'] with i hi
    simpa [factorMap, commutatorElement_eq_one_iff_commute, mem_centralizer_singleton_iff]
      using hi
  · refine .of_forall fun i ⟨c, hc⟩ => hg ⟨g.1, ?_⟩
    rw [centralizerExtMap_true] at hc ⊢
    -- The second components: `1 = v`, since the image of `(c, v)` is `(f c, v)`.
    exact Prod.ext rfl (congrArg Prod.snd hc :)

/-- If homomorphisms `fᵢ : G →* Kᵢ` eventually keep every nonidentity element of `G` along a
filter, the induced homomorphisms `G(u, ℤⁿ) →* Kᵢ(fᵢ u, ℤⁿ)` eventually keep every nonidentity
element of `G(u, ℤⁿ)`. For a constant family of one injective homomorphism this is
`map_injective`. -/
theorem eventually_map_ne_one {ι : Type*} {l : Filter ι} {K : ι → Type*} [∀ i, Group (K i)]
    {f : ∀ i, G →* K i} (hf : ∀ g : G, g ≠ 1 → ∀ᶠ i in l, f i g ≠ 1) (u : G) (n : ℕ)
    {x : CentralizerExt u n} (hx : x ≠ 1) : ∀ᶠ i in l, map (f i) u n x ≠ 1 := by
  simp only [map_eq_pushoutIMap]
  refine Monoid.PushoutI.eventually_map_ne_one _ (fun i => centralizerExtMap_injective (f i u) n)
    (fun h hh => ?_) (fun b _ hg => eventually_factorMap_notMem_range hf u n b hg) hx
  filter_upwards [hf h (Subtype.coe_ne_coe.2 hh)] with i hi h1
  exact hi (by simpa using congrArg Subtype.val h1)

/-- The homomorphism of extensions of centralizers induced by an injective homomorphism is
injective. -/
theorem map_injective {f : G →* K} (hf : Function.Injective f) (u : G) (n : ℕ) :
    Function.Injective (map f u n) :=
  (injective_iff_map_eq_one _).2 fun _ hx => by_contra fun hne => Filter.eventually_pure.1
    (eventually_map_ne_one (l := pure ()) (K := fun _ => K) (f := fun _ => f)
      (fun _ hg => Filter.eventually_pure.2 ((map_ne_one_iff f hf).2 hg)) u n hne) hx

/-- The homomorphism of extensions of centralizers induced by `f` is injective exactly when `f`
is. -/
theorem map_injective_iff {f : G →* K} (u : G) (n : ℕ) :
    Function.Injective (map f u n) ↔ Function.Injective f := by
  refine ⟨fun h => ?_, fun hf => map_injective hf u n⟩
  rw [← (of_injective (u := f u) (n := n)).of_comp_iff, ← MonoidHom.coe_comp, ← map_comp_of]
  exact h.comp of_injective

end CentralizerExt

end TauCeti.LimitGroup
