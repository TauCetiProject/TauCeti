/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Perfectoid.FontaineTheta
public import TauCeti.RingTheory.Perfectoid.Untilt
public import TauCeti.RingTheory.WittVector.TeichmullerCoeff

/-!
# Functoriality of the tilt, the sharp map and Fontaine's map

A ring homomorphism `f : A →+* B` sends `p A` into `p B`, so it induces a ring homomorphism
`ModP.map p f : A ⧸ p → B ⧸ p` and, coordinatewise on compatible systems of `p`-th roots, a ring
homomorphism of tilts `PreTilt.map p f : A♭ → B♭`. When `A` and `B` are `p`-adically complete,
the sharp map `x ↦ x♯` (Mathlib's `PreTilt.untilt`) and Fontaine's map
`θ : W(A♭) → A` (Mathlib's `WittVector.fontaineTheta`) are natural in `f`:

* `f (x♯) = (PreTilt.map p f x)♯`;
* `f (θ_A w) = θ_B (W(PreTilt.map p f) w)`.

The first identity holds because `x♯` is the `p`-adic limit of the `p ^ n`-th powers of lifts of
the coordinates of `x`, and `f` preserves these congruences. The second follows from the first,
since a ring homomorphism out of `W(A♭)` into a `p`-adically separated ring is determined by its
values on Teichmüller representatives (`WittVector.ringHom_ext_teichmuller`), and
`θ [x] = x♯`.

These identities let constructions on tilts (products, quotients, base change) be compared with
the corresponding constructions on the rings themselves.

## Main definitions

* `ModP.map p f : ModP A p →+* ModP B p`: reduction modulo `p` of a ring homomorphism.
* `PreTilt.map p f : PreTilt A p →+* PreTilt B p`: the induced homomorphism of tilts.

## Main results

* `PreTilt.coeff_map`: the coordinates of `PreTilt.map p f x` are the reductions of those of `x`.
* `PreTilt.map_id`, `PreTilt.map_comp`: functoriality.
* `PreTilt.untilt_map`: naturality of the sharp map, `(PreTilt.map p f x)♯ = f (x♯)`.
* `WittVector.fontaineTheta_map`: naturality of Fontaine's map.

## References

* B. Bhatt, M. Morrow, P. Scholze, *Integral `p`-adic Hodge theory*, Lemma 3.2.
* K. Česnavičius, P. Scholze, *Purity for flat cohomology*, §2.1.1.
-/

public section

open Ideal

variable {A B C : Type*} [CommRing A] [CommRing B] [CommRing C]

namespace ModP

variable (p : ℕ)

/-- The reduction modulo `p` of a ring homomorphism `f : A →+* B`, as a ring homomorphism
`A ⧸ p → B ⧸ p`; it is well defined because `f` maps `p A` into `p B`. -/
noncomputable def map (f : A →+* B) : ModP A p →+* ModP B p :=
  quotientMap _ f <| span_le.mpr <| Set.singleton_subset_iff.mpr <| by
    rw [SetLike.mem_coe, mem_comap, map_natCast]
    exact mem_span_singleton_self _

@[simp]
theorem map_mk (f : A →+* B) (a : A) :
    map p f (Ideal.Quotient.mk _ a) = Ideal.Quotient.mk _ (f a) :=
  quotientMap_mk ..

@[simp]
theorem map_id : map p (RingHom.id A) = RingHom.id (ModP A p) :=
  Ideal.Quotient.ringHom_ext <| RingHom.ext fun a ↦ by simp

theorem map_comp (g : B →+* C) (f : A →+* B) : map p (g.comp f) = (map p g).comp (map p f) :=
  Ideal.Quotient.ringHom_ext <| RingHom.ext fun a ↦ by simp

end ModP

namespace PreTilt

variable (p : ℕ) [Fact p.Prime] [Fact ¬IsUnit (p : A)] [Fact ¬IsUnit (p : B)]
  [Fact ¬IsUnit (p : C)]

/-- The ring homomorphism of tilts `A♭ → B♭` induced by a ring homomorphism `f : A →+* B`: it
reduces every coordinate of a compatible system of `p`-th roots in `A ⧸ p` along `f`. -/
noncomputable def map (f : A →+* B) : PreTilt A p →+* PreTilt B p :=
  Perfection.map p (ModP.map p f)

variable {p}

@[simp]
theorem coeff_map (f : A →+* B) (x : PreTilt A p) (n : ℕ) :
    coeff n (map p f x) = ModP.map p f (coeff n x) := by
  rw [coeff_def, coeff_def]
  -- `PreTilt A p` is by definition `Perfection (ModP A p) p`, and `map p f` is `Perfection.map`
  exact Perfection.coeff_map p (ModP.map p f) x n

variable (p) in
@[simp]
theorem map_id : map p (RingHom.id A) = RingHom.id (PreTilt A p) :=
  RingHom.ext fun x ↦ ext fun n ↦ by simp

variable (p) in
theorem map_comp (g : B →+* C) (f : A →+* B) :
    map p (g.comp f) = (map p g).comp (map p f) :=
  RingHom.ext fun x ↦ ext fun n ↦ by simp [ModP.map_comp]

/-- **Naturality of the sharp map**: for `p`-adically complete `A` and `B`, a ring homomorphism
`f : A →+* B` satisfies `(PreTilt.map p f x)♯ = f (x♯)`. -/
@[simp]
theorem untilt_map [IsAdicComplete (span {(p : A)}) A] [IsAdicComplete (span {(p : B)}) B]
    (f : A →+* B) (x : PreTilt A p) : (map p f x).untilt = f x.untilt := by
  rw [← teichmuller₀_equivPerfection]
  -- `x♯ ≡ y ^ p ^ n` modulo `p ^ (n + 1)` for a lift `y` of the `n`-th coordinate of `x`, and `f`
  -- preserves these congruences, so `f (x♯)` satisfies the characterisation of `(map p f x)♯`
  refine Perfection.teichmuller₀_spec fun n ↦ ⟨f (coeff n x).out, ?_, ?_⟩
  · rw [coeff_equivPerfection, coeff_map, ← Ideal.Quotient.mk_out (coeff n x), ModP.map_mk,
      Ideal.Quotient.mk_out]
  · have h := Perfection.teichmuller₀_sModEq (I := span {(p : A)}) (x := equivPerfection x)
      (y := (coeff n x).out) (by rw [Ideal.Quotient.mk_out, coeff_equivPerfection])
    rw [teichmuller₀_equivPerfection] at h
    simp only [SModEq.sub_mem, span_singleton_pow, mem_span_singleton] at h ⊢
    rw [dvd_sub_comm]
    simpa only [map_sub, map_pow, map_natCast] using map_dvd f h

end PreTilt

namespace WittVector

variable {p : ℕ} [Fact p.Prime] [Fact ¬IsUnit (p : A)] [Fact ¬IsUnit (p : B)]
  [IsAdicComplete (span {(p : A)}) A] [IsAdicComplete (span {(p : B)}) B]

/-- **Naturality of Fontaine's map**: for `p`-adically complete `A` and `B` and a ring
homomorphism `f : A →+* B`, `θ_B ∘ W(PreTilt.map p f) = f ∘ θ_A`. -/
theorem fontaineTheta_comp_map (f : A →+* B) :
    (fontaineTheta B p).comp (map (PreTilt.map p f)) = f.comp (fontaineTheta A p) :=
  ringHom_ext_teichmuller fun x ↦ by
    simp [map_teichmuller, fontaineTheta_teichmuller]

/-- **Naturality of Fontaine's map**, elementwise: `θ_B (W(PreTilt.map p f) w) = f (θ_A w)`. -/
@[simp]
theorem fontaineTheta_map (f : A →+* B) (w : WittVector p (PreTilt A p)) :
    fontaineTheta B p (map (PreTilt.map p f) w) = f (fontaineTheta A p w) :=
  congr($(fontaineTheta_comp_map f) w)

end WittVector
