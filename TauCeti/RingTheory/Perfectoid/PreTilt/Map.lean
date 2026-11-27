/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Perfectoid.FontaineTheta
public import TauCeti.RingTheory.Perfectoid.Untilt
public import TauCeti.RingTheory.Teichmuller
public import TauCeti.RingTheory.WittVector.MapEquiv
public import TauCeti.RingTheory.WittVector.Teichmuller.Coeff

import Mathlib.NumberTheory.Basic
import TauCeti.RingTheory.AdicCompletion.Pi

/-!
# Functoriality of the tilt, the sharp map and Fontaine's map

A ring homomorphism `f : A →+* B` sends `p A` into `p B`, so it induces a ring homomorphism
`ModP.map p f : A ⧸ p → B ⧸ p` and, coordinatewise on compatible systems of `p`-th roots, a ring
homomorphism of tilts `PreTilt.map p f : A♭ → B♭`. When `A` and `B` are `p`-adically complete,
the sharp map `x ↦ x♯` (Mathlib's `PreTilt.untilt`) and Fontaine's map
`θ : W(A♭) → A` (Mathlib's `WittVector.fontaineTheta`) are natural in `f`:

* `f (x♯) = (PreTilt.map p f x)♯`;
* `f (θ_A w) = θ_B (W(PreTilt.map p f) w)`.

The first identity is the case `I = (p)` of the naturality of the Teichmüller map
(`Perfection.teichmuller₀_map`): `x♯` is the `p`-adic limit of the `p ^ n`-th powers of lifts of
the coordinates of `x`, and `f` preserves these congruences. The second follows from the first,
since a ring homomorphism out of `W(A♭)` into a `p`-adically separated ring is determined by its
values on Teichmüller representatives (`WittVector.ringHom_ext_teichmuller`), and
`θ [x] = x♯`.

These identities let constructions on tilts (products, quotients, base change) be compared with
the corresponding constructions on the rings themselves.

## Main definitions

* `ModP.map p f : ModP A p →+* ModP B p`: reduction modulo `p` of a ring homomorphism.
* `PreTilt.map p f : PreTilt A p →+* PreTilt B p`: the induced homomorphism of tilts.
* `PreTilt.mapEquiv p e : PreTilt A p ≃+* PreTilt B p`: the induced isomorphism of tilts, for a
  ring isomorphism `e`.

## Main results

* `PreTilt.coeff_map`: the coordinates of `PreTilt.map p f x` are the reductions of those of `x`.
* `PreTilt.map_id`, `PreTilt.map_comp`: functoriality.
* `PreTilt.untilt_natural`: naturality of the sharp map, `(PreTilt.map p f x)♯ = f (x♯)`.
* `PreTilt.apply_untilt_eq_of_map_eq`: for `f : A →+* C` and `g : B →+* C` with `C` only
  `p`-adically Hausdorff, elements of `A♭` and `B♭` with the same image in `C♭` have sharps with the
  same image in `C`.
* `WittVector.theta_natural`: naturality of Fontaine's map.
* `WittVector.map_mapEquiv_ker_fontaineTheta`: a ring isomorphism `e : A ≃+* B` induces an
  isomorphism `W(A♭) ≃+* W(B♭)` carrying `ker θ_A` onto `ker θ_B`.

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

variable (p) in
/-- The ring isomorphism of tilts `A♭ ≃+* B♭` induced by a ring isomorphism `e : A ≃+* B`: it is
`PreTilt.map p e`, with inverse `PreTilt.map p e.symm`. -/
noncomputable def mapEquiv (e : A ≃+* B) : PreTilt A p ≃+* PreTilt B p :=
  .ofRingHom (map p e) (map p e.symm)
    (by rw [← map_comp, RingEquiv.comp_symm, map_id])
    (by rw [← map_comp, RingEquiv.symm_comp, map_id])

@[simp]
theorem coe_mapEquiv (e : A ≃+* B) :
    (mapEquiv p e : PreTilt A p →+* PreTilt B p) = map p e :=
  (rfl)

@[simp]
theorem mapEquiv_apply (e : A ≃+* B) (x : PreTilt A p) : mapEquiv p e x = map p e x :=
  (rfl)

@[simp]
theorem mapEquiv_symm (e : A ≃+* B) : (mapEquiv p e).symm = mapEquiv p e.symm :=
  (rfl)

/-- **Naturality of the sharp map**: for `p`-adically complete `A` and `B`, a ring homomorphism
`f : A →+* B` satisfies `(PreTilt.map p f x)♯ = f (x♯)`. -/
@[simp]
theorem untilt_natural [IsAdicComplete (span {(p : A)}) A] [IsAdicComplete (span {(p : B)}) B]
    (f : A →+* B) (x : PreTilt A p) : (map p f x).untilt = f x.untilt := by
  rw [← teichmuller₀_equivPerfection, ← teichmuller₀_equivPerfection]
  refine Eq.trans ?_ (Perfection.teichmuller₀_map (J := span {(p : B)}) f ?_ (equivPerfection x))
  · -- `PreTilt.map p f` is `Perfection.map` of `ModP.map p f`, an `Ideal.quotientMap`
    congr 1
    ext n
    simp [ModP.map]
  · rw [← Ideal.map_le_iff_le_comap, Ideal.map_span, Set.image_singleton, map_natCast]

/-- Let `f : A →+* C` and `g : B →+* C` be ring homomorphisms out of `p`-adically complete rings
into a `p`-adically Hausdorff ring `C`, which need not be complete. If `u ∈ A♭` and `v ∈ B♭` have
the same image in `C♭`, then `f (u♯) = g (v♯)`. -/
theorem apply_untilt_eq_of_map_eq [IsAdicComplete (span {(p : A)}) A]
    [IsAdicComplete (span {(p : B)}) B] [IsHausdorff (span {(p : C)}) C] {f : A →+* C}
    {g : B →+* C} {u : PreTilt A p} {v : PreTilt B p} (h : map p f u = map p g v) :
    f u.untilt = g v.untilt := by
  refine (IsHausdorff.eq_iff_smodEq (I := span {(p : C)})).mpr fun k ↦ ?_
  rw [TauCeti.sModEq_span_singleton_pow_iff]
  -- `u♯` and `v♯` are the `p ^ k`-th powers of the sharps of the `p ^ k`-th roots of `u` and `v`,
  -- whose images under `f` and `g` agree modulo `p`
  have hdvd : (p : C) ∣ f (untilt ((frobeniusEquiv (PreTilt A p) p).symm^[k] u)) -
      g (untilt ((frobeniusEquiv (PreTilt B p) p).symm^[k] v)) := by
    have hk := congr(coeff k $h)
    rwa [coeff_map, coeff_map, coeff_eq_mk_untilt_iterate, coeff_eq_mk_untilt_iterate,
      ModP.map_mk, ModP.map_mk, Ideal.Quotient.eq, Ideal.mem_span_singleton] at hk
  rw [← untilt_iterate_frobeniusEquiv_symm_pow u k, ← untilt_iterate_frobeniusEquiv_symm_pow v k,
    map_pow, map_pow]
  exact (pow_dvd_pow _ k.le_succ).trans (dvd_sub_pow_of_dvd_sub hdvd k)

end PreTilt

namespace WittVector

variable {p : ℕ} [Fact p.Prime] [Fact ¬IsUnit (p : A)] [Fact ¬IsUnit (p : B)]
  [IsAdicComplete (span {(p : A)}) A] [IsAdicComplete (span {(p : B)}) B]

/-- **Naturality of Fontaine's map**: for `p`-adically complete `A` and `B` and a ring
homomorphism `f : A →+* B`, `θ_B ∘ W(PreTilt.map p f) = f ∘ θ_A`. -/
theorem theta_natural_comp (f : A →+* B) :
    (fontaineTheta B p).comp (map (PreTilt.map p f)) = f.comp (fontaineTheta A p) :=
  ringHom_ext_teichmuller fun x ↦ by
    simp [map_teichmuller, fontaineTheta_teichmuller]

/-- **Naturality of Fontaine's map**, elementwise: `θ_B (W(PreTilt.map p f) w) = f (θ_A w)`. -/
@[simp]
theorem theta_natural (f : A →+* B) (w : WittVector p (PreTilt A p)) :
    fontaineTheta B p (map (PreTilt.map p f) w) = f (fontaineTheta A p w) :=
  congr($(theta_natural_comp f) w)

/-- **A ring isomorphism carries the kernel of Fontaine's map onto the kernel of Fontaine's map.**
For `p`-adically complete `A` and `B` and `e : A ≃+* B`, the isomorphism `W(A♭) ≃+* W(B♭)` induced
by `e` carries `ker θ_A` onto `ker θ_B`, by naturality of `θ`. -/
theorem map_mapEquiv_ker_fontaineTheta (e : A ≃+* B) :
    (RingHom.ker (fontaineTheta A p)).map (mapEquiv (PreTilt.mapEquiv p e)) =
      RingHom.ker (fontaineTheta B p) := by
  ext w
  simp [← comap_symm, RingHom.mem_ker]

end WittVector
