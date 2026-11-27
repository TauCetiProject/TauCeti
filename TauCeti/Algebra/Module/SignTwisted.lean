/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Subgroup.Ker
public import Mathlib.Algebra.Module.Submodule.Lattice
public import Mathlib.Algebra.Module.Pi
public import TauCeti.Data.ZMod.IntUnitsPower
import TauCeti.Algebra.CharP.Invertible
import TauCeti.Data.ZMod.Two
import TauCeti.GroupTheory.Index.DomRestrict

/-!
# Maps twisted by sign characters and their splitting on double covers

Let `j : G →+ A` be a homomorphism from a commutative group `G` to a monoid `A`, such as the
inclusion of a lattice `Λ` in `ℂ`, and let `χ : G →+ ZMod 2` be a sign character. A map
`v : A → E` is *twisted by `χ` along `j`* if `v (z + j g) = (-1) ^ χ g • v z` for all `g` and `z`,
the sign being `TauCeti.hilbertSign (χ g)`. For `A = ℂ` and a lattice `Λ`, these are the sections of
the flat real line bundle of `χ` over the torus `ℂ / Λ`; for `χ = 0`, the `Λ`-periodic maps. They
form a submodule `TauCeti.signTwisted R j χ` of `A → E`.

Twisted maps pull back along homomorphisms `f : G' →+ G`
(`TauCeti.signTwisted_le_signTwisted_comp`), with equality when `f` is surjective, as for a change
of basis of the lattice (`TauCeti.signTwisted_comp_of_surjective`).

The double cover of the torus defined by a nonzero sign character `ι` is `ℂ / ker ι`. When `2` is
invertible in the scalars, a map on it twisted by the restriction of `χ` is uniquely the sum of a
map twisted by `χ` and a map twisted by `χ + ι` along all of `Λ`, the two sign characters
restricting to the same one on `ker ι`:

* `TauCeti.disjoint_signTwisted_add`: the two summands meet only in `0`;
* `TauCeti.signTwisted_domRestrict_ker_inf_eq_sup`: for every submodule `S` of `A → E` invariant
  under the translations by `j`, such as the solutions of a translation-invariant linear equation,
  the maps of `S` twisted along `ker ι` are the sums of maps of `S` twisted by `χ` and by `χ + ι`.
  With `v₀ = v (· + j g₀)` for some `g₀` with `ι g₀ = 1` and `s` the sign of `χ g₀`, the summands
  are `(v + s v₀) / 2` and `(v - s v₀) / 2`.

So a translation-invariant equation has no nonzero solution twisted along `ker ι` exactly when it
has none twisted by `χ` and none twisted by `χ + ι`
(`TauCeti.signTwisted_domRestrict_ker_inf_eq_bot_iff`). Applying this twice, for a second sign
character `κ` not vanishing on `ker ι`, the equation has no nonzero periodic solution on the
four-fold cover `ker κ|ker ι` exactly when it has no nonzero solution twisted by any of `0`, `ι`,
`κ` and `κ + ι` (`TauCeti.signTwisted_zero_domRestrict_ker_domRestrict_ker_inf_eq_bot_iff`).
For a lattice of rank two these are the four sign characters, and the four-fold cover is `ℂ / 2Λ`.

This is the kernel-level comparison behind Taubes's labels of square-zero tori: for any
translation-invariant subspace, such as the kernel of the normal operator, the maps twisted along
`ker ι` by the restriction of `χ` split into those twisted by `χ` and by `χ + ι`.

## References

* C. H. Taubes, *Counting pseudo-holomorphic submanifolds in dimension 4*, J. Differential Geom.
  **44** (1996), 818–893.
-/

public section

namespace TauCeti

variable (R : Type*) {G G' A E : Type*} [Ring R] [AddCommGroup G] [AddCommGroup G'] [AddMonoid A]
  [AddCommGroup E] [Module R E]

/-- The maps `v : A → E` **twisted by the sign character `χ` along `j`**:
`v (z + j g) = (-1) ^ χ g • v z` for all `g` and `z`. For the inclusion `j` of a lattice of `ℂ`,
these are the sections of the flat real line bundle of `χ` over the torus. -/
def signTwisted (j : G →+ A) (χ : G →+ ZMod 2) : Submodule R (A → E) where
  carrier := {v | ∀ g z, v (z + j g) = hilbertSign (χ g) • v z}
  add_mem' {v w} hv hw g z := by simp [hv g z, hw g z]
  zero_mem' g z := by simp
  smul_mem' c v hv g z := by simp [hv g z, smul_comm c (hilbertSign (χ g))]

variable {R} {j : G →+ A} {χ : G →+ ZMod 2} {v : A → E}

@[simp]
theorem mem_signTwisted :
    v ∈ signTwisted R j χ ↔ ∀ g z, v (z + j g) = hilbertSign (χ g) • v z :=
  Iff.rfl

/-- Maps twisted by the trivial sign character are the periodic maps. -/
theorem mem_signTwisted_zero : v ∈ signTwisted R j 0 ↔ ∀ g z, v (z + j g) = v z := by
  simp

/-- **Pullback of twisted maps.** A map twisted by `χ` along `j` is twisted by `χ ∘ f` along
`j ∘ f`, for every homomorphism `f`, such as the inclusion of the lattice of a finite cover. -/
theorem signTwisted_le_signTwisted_comp (f : G' →+ G) :
    (signTwisted R j χ : Submodule R (A → E)) ≤ signTwisted R (j.comp f) (χ.comp f) :=
  fun _ hv g z ↦ hv (f g) z

/-- **Change of trivialization.** Twisting along a surjective reparametrization of the lattice,
such as a change of its basis, gives the same maps. -/
theorem signTwisted_comp_of_surjective {f : G' →+ G} (hf : Function.Surjective f) :
    (signTwisted R (j.comp f) (χ.comp f) : Submodule R (A → E)) = signTwisted R j χ := by
  refine le_antisymm (fun v hv g z ↦ ?_) (signTwisted_le_signTwisted_comp f)
  obtain ⟨g', rfl⟩ := hf g
  exact hv g' z

/-- Restricting the lattice to a subgroup `H` keeps twisted maps twisted, by the restriction of the
sign character. -/
theorem signTwisted_le_signTwisted_domRestrict (H : AddSubgroup G) :
    (signTwisted R j χ : Submodule R (A → E)) ≤
      signTwisted R (j.domRestrict H) (χ.domRestrict H) :=
  signTwisted_le_signTwisted_comp H.subtype

/-- Translating a twisted map by an element of `A` commuting with the image of `j` keeps it
twisted. -/
theorem translate_mem_signTwisted (hv : v ∈ signTwisted R j χ) {a : A}
    (ha : ∀ g, j g + a = a + j g) : (fun z ↦ v (z + a)) ∈ signTwisted R j χ := by
  intro g z
  simp only [add_assoc, ha g]
  rw [← add_assoc, hv g]

/-- **Extension of twisted maps from a double cover.** If `v` is twisted along `ker ι` by the
restriction of `χ`, and the twisting law holds at one `g₀` with `ι g₀ = 1`, then `v` is twisted by
`χ` along all of `G`. -/
theorem mem_signTwisted_of_mem_signTwisted_domRestrict_ker {ι : G →+ ZMod 2} {g₀ : G}
    (hg₀ : ι g₀ = 1) (hv : v ∈ signTwisted R (j.domRestrict ι.ker) (χ.domRestrict ι.ker))
    (h₀ : ∀ z, v (z + j g₀) = hilbertSign (χ g₀) • v z) : v ∈ signTwisted R j χ := by
  intro g z
  by_cases hg : ι g = 0
  · exact hv ⟨g, hg⟩ z
  · -- Otherwise `g - g₀` lies in `ker ι`, and the law at `g` is the law at `g₀` and at `g - g₀`.
    have hk : ι (g - g₀) = 0 := by rw [map_sub, hg₀, ZMod.ne_zero_iff_eq_one.mp hg, sub_self]
    have hj : j g = j g₀ + j (g - g₀) := by rw [← map_add, add_sub_cancel]
    have := hv ⟨g - g₀, hk⟩ (z + j g₀)
    simp only [AddMonoidHom.domRestrict_apply] at this
    rw [hj, ← add_assoc, this, h₀, smul_smul, ← hilbertSign_add, ← map_add, sub_add_cancel]

/-- A map twisted along `ker ι` is invariant under the translation by twice any `g₀`: twice `g₀`
lies in `ker ι`, and every sign character vanishes on it. -/
private theorem apply_add_add_eq_of_mem_signTwisted_domRestrict_ker {ι : G →+ ZMod 2}
    (hv : v ∈ signTwisted R (j.domRestrict ι.ker) (χ.domRestrict ι.ker)) (g₀ : G) (z : A) :
    v (z + j g₀ + j g₀) = v z := by
  have h2 : ∀ x : ZMod 2, x + x = 0 := by decide
  have := hv ⟨g₀ + g₀, by rw [AddMonoidHom.mem_ker, map_add, h2]⟩ z
  simp only [AddMonoidHom.domRestrict_apply, map_add, h2, hilbertSign_zero, one_smul] at this
  rw [add_assoc, this]

variable [Invertible (2 : R)]

/-- **Twists differing by a nonzero sign character are independent.** No nonzero map is twisted
both by `χ` and by `χ + ι` when `ι ≠ 0` and `2` is invertible. -/
theorem disjoint_signTwisted_add {ι : G →+ ZMod 2} (hι : ι ≠ 0) :
    Disjoint (signTwisted R j χ) (signTwisted R j (χ + ι) : Submodule R (A → E)) := by
  rw [Submodule.disjoint_def]
  intro v h₁ h₂
  obtain ⟨g₀, hg₀⟩ := ι.exists_eq_one_of_ne_zero hι
  funext z
  have h := (h₁ g₀ z).symm.trans (h₂ g₀ z)
  rw [AddMonoidHom.add_apply, hg₀, hilbertSign_add_one, Units.neg_smul] at h
  have := eq_zero_of_eq_neg_of_invertible_two (R := R) h
  rwa [smul_eq_zero_iff_eq] at this

/-- **Splitting of twisted maps on a double cover.** Let `S` be a submodule of `A → E` invariant
under the translations by `j`, and `ι` a sign character. The maps of `S` twisted along `ker ι` by
the restriction of `χ` are the sums of maps of `S` twisted by `χ` and by `χ + ι` along all of `G`.
For `ι ≠ 0` the sum is direct (`TauCeti.disjoint_signTwisted_add`). -/
theorem signTwisted_domRestrict_ker_inf_eq_sup {ι : G →+ ZMod 2} {S : Submodule R (A → E)}
    (hS : ∀ g, ∀ v ∈ S, (fun z ↦ v (z + j g)) ∈ S) :
    signTwisted R (j.domRestrict ι.ker) (χ.domRestrict ι.ker) ⊓ S =
      signTwisted R j χ ⊓ S ⊔ signTwisted R j (χ + ι) ⊓ S := by
  refine le_antisymm ?_ (sup_le (inf_le_inf_right _ (signTwisted_le_signTwisted_domRestrict _)) ?_)
  · rintro v ⟨hv, hvS⟩
    rcases eq_or_ne ι 0 with rfl | hι
    · -- For `ι = 0` the cover is trivial: `ker ι` is all of `G`.
      exact Submodule.mem_sup_left ⟨fun g z ↦ hv ⟨g, by simp⟩ z, hvS⟩
    obtain ⟨g₀, hg₀⟩ := ι.exists_eq_one_of_ne_zero hι
    -- With `s` the sign of `χ g₀` and `w = v (· + j g₀)`, the summands are `(v ± s w) / 2`.
    set s := hilbertSign (χ g₀) with hs
    set w : A → E := fun z ↦ v (z + j g₀)
    have hw : w ∈ signTwisted R (j.domRestrict ι.ker) (χ.domRestrict ι.ker) :=
      translate_mem_signTwisted hv fun g ↦ by
        simp only [AddMonoidHom.domRestrict_apply, ← map_add, add_comm]
    have hvw : ∀ z, v (z + j g₀) = w z := fun _ ↦ rfl
    have hww : ∀ z, w (z + j g₀) = v z :=
      apply_add_add_eq_of_mem_signTwisted_domRestrict_ker hv g₀
    have hsw : s • w ∈ signTwisted R (j.domRestrict ι.ker) (χ.domRestrict ι.ker) := by
      rw [Units.smul_def]; exact Submodule.smul_of_tower_mem _ _ hw
    have hswS : s • w ∈ S := by
      rw [Units.smul_def]; exact Submodule.smul_of_tower_mem _ _ (hS g₀ v hvS)
    have h₁ : v + s • w ∈ signTwisted R j χ :=
      mem_signTwisted_of_mem_signTwisted_domRestrict_ker hg₀ (add_mem hv hsw) fun z ↦ by
        simp only [Pi.add_apply, Pi.smul_apply, ← hs, hvw, hww, smul_add, smul_smul,
          Int.units_mul_self, one_smul, add_comm]
    have h₂ : v - s • w ∈ signTwisted R j (χ + ι) :=
      mem_signTwisted_of_mem_signTwisted_domRestrict_ker (χ := χ + ι) hg₀
        (by rw [AddMonoidHom.domRestrict_ker_add_self]; exact sub_mem hv hsw) fun z ↦ by
        rw [AddMonoidHom.add_apply, hg₀, hilbertSign_add_one]
        simp only [Pi.sub_apply, Pi.smul_apply, ← hs, hvw, hww, smul_sub, smul_smul, neg_mul,
          Int.units_mul_self, Units.neg_smul, one_smul, sub_neg_eq_add, neg_add_eq_sub]
    have hv₂ : v = ⅟(2 : R) • (v + s • w) + ⅟(2 : R) • (v - s • w) := by
      rw [← smul_add, add_add_sub_cancel, ← two_smul R v, smul_smul, invOf_mul_self, one_smul]
    rw [hv₂]
    exact Submodule.add_mem_sup ⟨Submodule.smul_mem _ _ h₁, S.smul_mem _ (add_mem hvS hswS)⟩
      ⟨Submodule.smul_mem _ _ h₂, S.smul_mem _ (sub_mem hvS hswS)⟩
  · refine inf_le_inf_right _ ?_
    rw [← AddMonoidHom.domRestrict_ker_add_self χ ι]
    exact signTwisted_le_signTwisted_domRestrict _

/-- Without a constraint, the maps twisted along `ker ι` by the restriction of `χ` are the sums of
maps twisted by `χ` and by `χ + ι`. -/
theorem signTwisted_domRestrict_ker_eq_sup (ι : G →+ ZMod 2) :
    signTwisted R (j.domRestrict ι.ker) (χ.domRestrict ι.ker) =
      (signTwisted R j χ ⊔ signTwisted R j (χ + ι) : Submodule R (A → E)) := by
  simpa using signTwisted_domRestrict_ker_inf_eq_sup (R := R) (j := j) (χ := χ) (ι := ι)
    (S := ⊤) fun _ _ _ ↦ trivial

/-- **Nondegeneracy on a double cover.** A translation-invariant submodule `S`, such as the
solutions of a translation-invariant linear equation, has no nonzero map twisted along `ker ι` by
the restriction of `χ` exactly when it has none twisted by `χ` and none twisted by `χ + ι`. -/
theorem signTwisted_domRestrict_ker_inf_eq_bot_iff {ι : G →+ ZMod 2} {S : Submodule R (A → E)}
    (hS : ∀ g, ∀ v ∈ S, (fun z ↦ v (z + j g)) ∈ S) :
    signTwisted R (j.domRestrict ι.ker) (χ.domRestrict ι.ker) ⊓ S = ⊥ ↔
      signTwisted R j χ ⊓ S = ⊥ ∧ signTwisted R j (χ + ι) ⊓ S = ⊥ := by
  rw [signTwisted_domRestrict_ker_inf_eq_sup hS, sup_eq_bot_iff]

/-- **Nondegeneracy on the four-fold cover.** Let `ι` and `κ` be sign characters and `K` the
kernel of the restriction of `κ` to `ker ι`. A translation-invariant submodule `S` has no nonzero
periodic map along `K` exactly when it has no nonzero map twisted by any of `0`, `ι`, `κ` and
`κ + ι`. When `ι ≠ 0` and `κ` does not vanish on `ker ι`, `K` has index four; for a lattice of rank
two these are then its four sign characters and `K = 2G`. -/
theorem signTwisted_zero_domRestrict_ker_domRestrict_ker_inf_eq_bot_iff {ι κ : G →+ ZMod 2}
    {S : Submodule R (A → E)} (hS : ∀ g, ∀ v ∈ S, (fun z ↦ v (z + j g)) ∈ S) :
    signTwisted R ((j.domRestrict ι.ker).domRestrict (κ.domRestrict ι.ker).ker) 0 ⊓ S = ⊥ ↔
      signTwisted R j 0 ⊓ S = ⊥ ∧ signTwisted R j ι ⊓ S = ⊥ ∧
        signTwisted R j κ ⊓ S = ⊥ ∧ signTwisted R j (κ + ι) ⊓ S = ⊥ := by
  have h₀ := signTwisted_domRestrict_ker_inf_eq_bot_iff (χ := 0) (ι := ι) hS
  have h := signTwisted_domRestrict_ker_inf_eq_bot_iff (χ := 0) (ι := κ.domRestrict ι.ker)
    (j := j.domRestrict ι.ker) fun g ↦ hS g
  have hz₀ : (0 : G →+ ZMod 2).domRestrict ι.ker = 0 := by ext; simp
  have hz : (0 : ι.ker →+ ZMod 2).domRestrict (κ.domRestrict ι.ker).ker = 0 := by
    ext; simp only [AddMonoidHom.domRestrict_apply, AddMonoidHom.zero_apply]
  rw [zero_add, hz₀] at h₀
  rw [zero_add, hz] at h
  rw [h, h₀, signTwisted_domRestrict_ker_inf_eq_bot_iff hS, and_assoc]

end TauCeti
