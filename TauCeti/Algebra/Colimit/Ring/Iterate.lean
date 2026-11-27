/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Colimit.DirectLimit

/-!
# The colimit of a semiring along an endomorphism

For a ring endomorphism `φ` of a semiring `R`, the *iterate colimit* `φ.IterateColimit` is the
sequential colimit `R → R → R → ⋯` whose transition maps are all `φ`. Writing `mk φ n x` for the
class of `x` in the `n`-th copy of `R`, it is the element `φ⁻ⁿ x`: the canonical map
`of φ = mk φ 0` intertwines `φ` with a ring automorphism `ringEquiv φ` of the colimit, whose
inverse sends `mk φ n x` to `mk φ (n + 1) x`. This is the universal way of making `φ` invertible.

Two elements of one stage agree in the colimit exactly when they agree after applying a power of
`φ` (`RingHom.IterateColimit.mk_eq_mk_iff`). A map `g : R →+* S` intertwining `φ` with an
endomorphism `ψ` of `S` induces a ring map of colimits (`RingHom.IterateColimit.map`). It is
injective exactly when every pair of elements of `R` identified by `g` after some power of `ψ`
is identified by some power of `φ`, and surjective exactly when some power of `ψ` carries every
element of `S` into the image of `g`.

For the `p`-th power map of a ring in which `p` vanishes this colimit is the perfection
(`TauCeti.ColimitPerfection`, compare `PerfectClosure`); for the Witt vector Frobenius `F` of
`W(A)` it is the ring `W(A)[1/F]` of Frobenius-inverted Witt vectors.

## Main definitions

* `RingHom.IterateColimit φ`: the colimit of `R → R → ⋯` along `φ`.
* `RingHom.IterateColimit.mk φ n`, `RingHom.IterateColimit.of φ`: the maps from the stages.
* `RingHom.IterateColimit.lift`: the universal property of the colimit.
* `RingHom.IterateColimit.ringEquiv φ`: the automorphism of the colimit induced by `φ`.
* `RingHom.IterateColimit.map`: the map of colimits induced by a map intertwining endomorphisms.

## Main results

* `RingHom.IterateColimit.mk_eq_mk_iff`: `mk φ n x = mk φ n y` iff `φᵏ x = φᵏ y` for some `k`.
* `RingHom.IterateColimit.injective_of_iff`, `RingHom.IterateColimit.bijective_of_iff`: the map
  from `R` to the colimit is injective, resp. bijective, exactly when `φ` is.
* `RingHom.IterateColimit.injective_map_iff`, `RingHom.IterateColimit.surjective_map_iff`:
  criteria for the induced map of colimits to be injective or surjective.
-/

public noncomputable section

namespace RingHom

variable {R : Type*} [Semiring R] (φ : R →+* R)

namespace IterateColimit

/-- The transition maps `φ ^ (n - m)` of the direct system defining the iterate colimit. -/
def transition (m n : ℕ) (_ : m ≤ n) : R →+* R :=
  φ ^ (n - m)

theorem transition_apply {m n : ℕ} (h : m ≤ n) (x : R) : transition φ m n h x = φ^[n - m] x := by
  rw [transition, coe_pow]

instance directedSystem : DirectedSystem (fun _ : ℕ ↦ R) (transition φ · · ·) where
  map_self x := by simp [transition_apply]
  map_map {k j i} hij hjk x := by
    simp only [transition_apply, ← Function.iterate_add_apply]
    congr 1
    omega

end IterateColimit

/-- The *iterate colimit* of a ring endomorphism `φ` of `R`: the sequential colimit of
`R → R → R → ⋯` along `φ`, in which `φ` becomes invertible. It is an abbreviation so that it
inherits the (commutative) semiring or ring structure of the direct limit. -/
abbrev IterateColimit : Type _ :=
  DirectLimit (fun _ : ℕ ↦ R) (IterateColimit.transition φ)

namespace IterateColimit

/-- The map from the `n`-th copy of `R` to the iterate colimit; `mk φ n x` is `φ⁻ⁿ x`. -/
def mk (n : ℕ) : R →+* φ.IterateColimit :=
  DirectLimit.Ring.of (fun _ : ℕ ↦ R) (transition φ) n

/-- The canonical map from `R` to its iterate colimit along `φ`. -/
def of : R →+* φ.IterateColimit :=
  mk φ 0

@[simp]
theorem mk_zero : mk φ 0 = of φ :=
  (rfl)

variable {φ}

/-- Every element of the iterate colimit is `mk φ n x` for some stage `n` and `x : R`. -/
theorem exists_eq_mk (z : φ.IterateColimit) : ∃ (n : ℕ) (x : R), z = mk φ n x :=
  DirectLimit.exists_eq_mk _ z

/-- Two elements of the iterate colimit come from a common stage. -/
theorem exists_eq_mk₂ (z w : φ.IterateColimit) :
    ∃ (n : ℕ) (x y : R), z = mk φ n x ∧ w = mk φ n y :=
  DirectLimit.exists_eq_mk₂ _ z w

/-- The class of `φᵏ x` in the `(n + k)`-th copy of `R` is the class of `x` in the `n`-th. -/
@[simp]
theorem mk_add_iterate (n k : ℕ) (x : R) : mk φ (n + k) (φ^[k] x) = mk φ n x := by
  have h := DirectLimit.Ring.of_f (G := fun _ : ℕ ↦ R) (f := transition φ)
    (Nat.le_add_right n k) x
  rwa [transition_apply, Nat.add_sub_cancel_left] at h

@[simp]
theorem mk_succ_apply (n : ℕ) (x : R) : mk φ (n + 1) (φ x) = mk φ n x :=
  mk_add_iterate n 1 x

theorem of_eq_mk (n : ℕ) (x : R) : of φ x = mk φ n (φ^[n] x) := by
  rw [← mk_zero, ← mk_add_iterate 0 n x, zero_add]

/-- **Equality in the iterate colimit.** Two elements of the same stage agree in the colimit
exactly when they agree after applying some power of `φ`. -/
theorem mk_eq_mk_iff {n : ℕ} {x y : R} :
    mk φ n x = mk φ n y ↔ ∃ k : ℕ, φ^[k] x = φ^[k] y := by
  refine ⟨fun h ↦ ?_, fun ⟨k, hk⟩ ↦ ?_⟩
  · obtain ⟨i, hx, hy, hxy⟩ := Quotient.eq.1 h
    exact ⟨i - n, by simpa only [transition_apply] using hxy⟩
  · rw [← mk_add_iterate n k x, ← mk_add_iterate n k y, hk]

theorem mk_eq_zero_iff {n : ℕ} {x : R} : mk φ n x = 0 ↔ ∃ k : ℕ, φ^[k] x = 0 := by
  rw [← map_zero (mk φ n), mk_eq_mk_iff]
  simp only [iterate_map_zero]

theorem of_eq_of_iff {x y : R} : of φ x = of φ y ↔ ∃ k : ℕ, φ^[k] x = φ^[k] y :=
  mk_eq_mk_iff

theorem of_eq_zero_iff {x : R} : of φ x = 0 ↔ ∃ k : ℕ, φ^[k] x = 0 :=
  mk_eq_zero_iff

/-! ### The universal property -/

section Lift

variable {S : Type*} [Semiring S]

variable (φ) in
/-- **The universal property of the iterate colimit.** A sequence of ring maps `g n : R →+* S`
with `g (n + 1) ∘ φ = g n` induces a ring map from the iterate colimit, sending `mk φ n x` to
`g n x`. -/
def lift (g : ℕ → R →+* S) (hg : ∀ n x, g (n + 1) (φ x) = g n x) : φ.IterateColimit →+* S :=
  DirectLimit.Ring.lift (fun _ : ℕ ↦ R) (transition φ) S g fun m n hmn x ↦ by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
    rw [transition_apply, Nat.add_sub_cancel_left]
    clear hmn
    induction k with
    | zero => rfl
    | succ k ih => rw [Function.iterate_succ_apply', ← add_assoc, hg, ih]

@[simp]
theorem lift_mk (g : ℕ → R →+* S) (hg : ∀ n x, g (n + 1) (φ x) = g n x) (n : ℕ) (x : R) :
    lift φ g hg (mk φ n x) = g n x :=
  (rfl)

@[simp]
theorem lift_of (g : ℕ → R →+* S) (hg : ∀ n x, g (n + 1) (φ x) = g n x) (x : R) :
    lift φ g hg (of φ x) = g 0 x :=
  (rfl)

/-- Ring maps out of the iterate colimit agree once they agree on every stage. -/
theorem hom_ext {g₁ g₂ : φ.IterateColimit →+* S} (h : ∀ n, g₁.comp (mk φ n) = g₂.comp (mk φ n)) :
    g₁ = g₂ :=
  DirectLimit.Ring.hom_ext _ h

end Lift

/-! ### The automorphism induced by `φ` -/

variable (φ) in
/-- The ring automorphism of the iterate colimit induced by `φ`: it sends `mk φ n x` to
`mk φ n (φ x)`, and its inverse sends `mk φ n x` to `mk φ (n + 1) x`. -/
def ringEquiv : φ.IterateColimit ≃+* φ.IterateColimit :=
  RingEquiv.ofRingHom
    (lift φ (fun n ↦ (mk φ n).comp φ) fun n x ↦ by simp)
    (lift φ (fun n ↦ mk φ (n + 1)) fun n x ↦ by simp)
    (hom_ext fun n ↦ by ext x; simp)
    (hom_ext fun n ↦ by ext x; simp)

@[simp]
theorem ringEquiv_mk (n : ℕ) (x : R) : ringEquiv φ (mk φ n x) = mk φ n (φ x) :=
  (rfl)

@[simp]
theorem ringEquiv_symm_mk (n : ℕ) (x : R) : (ringEquiv φ).symm (mk φ n x) = mk φ (n + 1) x :=
  (rfl)

/-- The map from `R` to its iterate colimit intertwines `φ` with the induced automorphism. -/
@[simp]
theorem ringEquiv_of (x : R) : ringEquiv φ (of φ x) = of φ (φ x) :=
  ringEquiv_mk 0 x

@[simp]
theorem ringEquiv_symm_of (x : R) : (ringEquiv φ).symm (of φ x) = mk φ 1 x :=
  ringEquiv_symm_mk 0 x

/-- `of φ` is injective exactly when `φ` is. -/
theorem injective_of_iff : Function.Injective (of φ) ↔ Function.Injective φ := by
  refine ⟨fun h x y hxy ↦ h (of_eq_of_iff.2 ⟨1, hxy⟩), fun h x y hxy ↦ ?_⟩
  obtain ⟨k, hk⟩ := of_eq_of_iff.1 hxy
  exact (h.iterate k) hk

/-- **An invertible endomorphism needs no colimit**: `of φ` is bijective exactly when `φ` is. -/
theorem bijective_of_iff : Function.Bijective (of φ) ↔ Function.Bijective φ := by
  refine ⟨fun h ↦ ⟨injective_of_iff.1 h.1, fun x ↦ ?_⟩, fun h ↦ ⟨injective_of_iff.2 h.1, ?_⟩⟩
  · -- `mk φ 1 x` comes from some `y`, and then `x = φ y` because `φ` is injective.
    obtain ⟨y, hy⟩ := h.2 (mk φ 1 x)
    rw [of_eq_mk 1, Function.iterate_one, mk_eq_mk_iff] at hy
    obtain ⟨k, hk⟩ := hy
    exact ⟨y, (injective_of_iff.1 h.1).iterate k hk⟩
  · intro z
    obtain ⟨n, x, rfl⟩ := exists_eq_mk z
    obtain ⟨y, rfl⟩ := (h.2.iterate n) x
    exact ⟨y, of_eq_mk n y⟩

/-! ### Functoriality -/

section Map

variable {S T : Type*} [Semiring S] [Semiring T] {ψ : S →+* S} {χ : T →+* T}

variable (φ ψ) in
/-- The map of iterate colimits induced by a ring map `g : R →+* S` intertwining `φ` with `ψ`;
it sends `mk φ n x` to `mk ψ n (g x)`. -/
def map (g : R →+* S) (hg : Function.Semiconj g φ ψ) : φ.IterateColimit →+* ψ.IterateColimit :=
  lift φ (fun n ↦ (mk ψ n).comp g) fun n x ↦ by simp [hg x]

@[simp]
theorem map_mk (g : R →+* S) (hg : Function.Semiconj g φ ψ) (n : ℕ) (x : R) :
    map φ ψ g hg (mk φ n x) = mk ψ n (g x) :=
  (rfl)

@[simp]
theorem map_of (g : R →+* S) (hg : Function.Semiconj g φ ψ) (x : R) :
    map φ ψ g hg (of φ x) = of ψ (g x) :=
  (rfl)

@[simp]
theorem map_id : map φ φ (RingHom.id R) (Function.Semiconj.id_left) = RingHom.id _ :=
  hom_ext fun n ↦ by ext; simp

theorem map_comp (g : R →+* S) (hg : Function.Semiconj g φ ψ) (h : S →+* T)
    (hh : Function.Semiconj h ψ χ) :
    map φ χ (h.comp g) (hh.comp_left hg) = (map ψ χ h hh).comp (map φ ψ g hg) :=
  hom_ext fun n ↦ by ext; simp

/-- The induced map of colimits commutes with the automorphisms induced by `φ` and `ψ`. -/
theorem map_ringEquiv (g : R →+* S) (hg : Function.Semiconj g φ ψ) (z : φ.IterateColimit) :
    map φ ψ g hg (ringEquiv φ z) = ringEquiv ψ (map φ ψ g hg z) := by
  obtain ⟨n, x, rfl⟩ := exists_eq_mk z
  simp [hg x]

/-- **Injectivity of the induced map of colimits.** The map induced by `g` is injective exactly
when any two elements of `R` that `g` identifies after some power of `ψ` are already identified
by some power of `φ`. -/
theorem injective_map_iff (g : R →+* S) (hg : Function.Semiconj g φ ψ) :
    Function.Injective (map φ ψ g hg) ↔
      ∀ x y, (∃ k, ψ^[k] (g x) = ψ^[k] (g y)) → ∃ k, φ^[k] x = φ^[k] y := by
  refine ⟨fun h x y hxy ↦ of_eq_of_iff.1 (h ?_), fun h z w hzw ↦ ?_⟩
  · simpa only [map_of] using of_eq_of_iff.2 hxy
  · obtain ⟨n, x, y, rfl, rfl⟩ := exists_eq_mk₂ z w
    simp only [map_mk, mk_eq_mk_iff] at hzw
    exact mk_eq_mk_iff.2 (h x y hzw)

/-- **Surjectivity of the induced map of colimits.** The map induced by `g` is surjective exactly
when some power of `ψ` carries each element of `S` into the image of `g`. -/
theorem surjective_map_iff (g : R →+* S) (hg : Function.Semiconj g φ ψ) :
    Function.Surjective (map φ ψ g hg) ↔ ∀ y, ∃ k x, ψ^[k] y = g x := by
  refine ⟨fun h y ↦ ?_, fun h z ↦ ?_⟩
  · -- If `of ψ y = mk ψ n (g x)`, then `ψⁿ⁺ᵏ y = g (φᵏ x)` for some `k`.
    obtain ⟨z, hz⟩ := h (of ψ y)
    obtain ⟨n, x, rfl⟩ := exists_eq_mk z
    rw [map_mk, of_eq_mk n, mk_eq_mk_iff] at hz
    obtain ⟨k, hk⟩ := hz
    refine ⟨k + n, φ^[k] x, ?_⟩
    rw [Function.iterate_add_apply, ← hk, (hg.iterate_right k) x]
  · -- `mk ψ n y = mk ψ (n + k) (ψᵏ y) = mk ψ (n + k) (g x)`.
    obtain ⟨n, y, rfl⟩ := exists_eq_mk z
    obtain ⟨k, x, hx⟩ := h y
    exact ⟨mk φ (n + k) x, by rw [map_mk, ← hx, mk_add_iterate]⟩

end Map

end IterateColimit

end RingHom
