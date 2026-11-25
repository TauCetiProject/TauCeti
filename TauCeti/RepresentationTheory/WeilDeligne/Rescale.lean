/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.WeilDeligne.Special

/-!
# Rescaling the monodromy of a Weil–Deligne parameter

For a raw Weil–Deligne parameter `(V, r, N)` and a scalar `a`, the pair `(r, a N)` is again a
raw Weil–Deligne parameter (`TauCeti.WeilDeligneParameter.rescale`): `a N` is nilpotent and
satisfies the same conjugation relation. Rescaling is functorial in isomorphisms and composes
multiplicatively.

For `q ≥ 2` and finite inertia image, `(r, N) ≅ (r, a N)` for every `a ≠ 0` (Deligne 1973, proof
of §8.4.3). This file proves it for the special parameters `Sp(n)`, where the diagonal matrix
`diag(1, a, …, a^(n-1))` commutes with the Weil action and conjugates `N` to `a N`
(`TauCeti.WeilDeligneParameter.specialRescaleIso`). The hypothesis `q ≥ 2` is needed in general:
if some `r(w)` equals `1 + N`, as happens for `q = 1`, then every automorphism commuting with the
Weil action commutes with `N`, so a nonzero `N` is isomorphic to its rescaling by `a` only for
`a = 1` (`TauCeti.WeilDeligneParameter.eq_one_of_iso_rescale`).

## Main definitions

* `TauCeti.WeilDeligneParameter.rescale`: the parameter `(r, a N)`.
* `TauCeti.WeilDeligneParameter.Iso.rescale`: rescaling an isomorphism.
* `TauCeti.WeilDeligneParameter.specialRescaleIso`: `Sp(n) ≅ Sp(n)` rescaled by a unit `a`.

## Main results

* `TauCeti.WeilDeligneParameter.eq_one_of_iso_rescale`: if `r(w) = 1 + N` for some `w` and
  `N ≠ 0`, an isomorphism `(r, N) ≅ (r, a N)` forces `a = 1`.

## References

* P. Deligne, *Les constantes des équations fonctionnelles des fonctions L*, in *Modular functions
  of one variable II*, Lecture Notes in Math. 349 (1973), §8.4.1, p. 568, and the proof of §8.4.3,
  p. 569.
-/

public section

noncomputable section

namespace TauCeti

namespace WeilDeligneParameter

variable {E W V V' : Type*} [Field E] [Group W] [TopologicalSpace W]
  [AddCommGroup V] [Module E V] [AddCommGroup V'] [Module E V']
  {deg : W →* Multiplicative ℤ} {q : ℕ}

/-- **Rescaling the monodromy**: the parameter `(r, a N)` with the same Weil action. -/
def rescale (D : WeilDeligneParameter E W V deg q) (a : E) : WeilDeligneParameter E W V deg q where
  r := D.r
  isOpen_ker := D.isOpen_ker
  N := a • D.N
  isNilpotent_N := D.isNilpotent_N.smul a
  conj_N w := by
    rw [mul_smul_comm, smul_mul_assoc, D.conj_N, smul_comm]

@[simp]
theorem rescale_r (D : WeilDeligneParameter E W V deg q) (a : E) : (D.rescale a).r = D.r :=
  (rfl)

@[simp]
theorem rescale_N (D : WeilDeligneParameter E W V deg q) (a : E) : (D.rescale a).N = a • D.N :=
  (rfl)

@[simp]
theorem rescale_one (D : WeilDeligneParameter E W V deg q) : D.rescale 1 = D := by
  ext1 <;> simp

theorem rescale_rescale (D : WeilDeligneParameter E W V deg q) (a b : E) :
    (D.rescale a).rescale b = D.rescale (b * a) := by
  ext1 <;> simp [mul_smul]

/-- An isomorphism of parameters is also an isomorphism of their rescalings. -/
def Iso.rescale {D : WeilDeligneParameter E W V deg q} {D' : WeilDeligneParameter E W V' deg q}
    (f : Iso D D') (a : E) : Iso (D.rescale a) (D'.rescale a) where
  toRepresentationEquiv := f.toRepresentationEquiv
  comp_N := by
    rw [rescale_N, rescale_N, LinearMap.comp_smul, LinearMap.smul_comp]
    exact congrArg (a • ·) f.comp_N

@[simp]
theorem Iso.coe_rescale {D : WeilDeligneParameter E W V deg q}
    {D' : WeilDeligneParameter E W V' deg q} (f : Iso D D') (a : E) : ⇑(f.rescale a) = f :=
  (rfl)

/-- **Rescaling is not always trivial**: if some `r(w)` is `1 + N` and `N ≠ 0`, then an
isomorphism `(r, N) ≅ (r, a N)` forces `a = 1`. The isomorphism commutes with `r(w)`, hence with
`N`, while it conjugates `N` to `a N`. -/
theorem eq_one_of_iso_rescale (D : WeilDeligneParameter E W V deg q) {w : W}
    (hw : D.r w = 1 + D.N) (hN : D.N ≠ 0) {a : E} (f : Iso D (D.rescale a)) : a = 1 := by
  have hcomm : ∀ v, f (D.N v) = D.N (f v) := fun v ↦ by
    have h := f.map_r_apply w v
    rw [rescale_r, hw] at h
    simpa using h
  have hscale : ∀ v, D.N (f v) = a • D.N (f v) := fun v ↦
    (hcomm v).symm.trans (f.map_N_apply v)
  by_contra ha
  refine hN (LinearMap.ext fun v ↦ ?_)
  obtain ⟨u, rfl⟩ := EquivLike.surjective f v
  have h : (a - 1) • D.N (f u) = 0 := by rw [sub_smul, one_smul, ← hscale u, sub_self]
  rw [LinearMap.zero_apply]
  exact (smul_eq_zero.mp h).resolve_left (sub_ne_zero.mpr ha)

/-! ### Rescaling the special parameters -/

variable (hdeg : Continuous deg) (hq : (q : E) ≠ 0)

/-- The diagonal linear equivalence `eᵢ ↦ a ^ i • eᵢ` of `Fin n → E`. -/
private def diagPow (n : ℕ) (a : Eˣ) : (Fin n → E) ≃ₗ[E] (Fin n → E) :=
  LinearEquiv.piCongrRight fun i : Fin n ↦ LinearEquiv.smulOfUnit (a ^ (i : ℕ))

private theorem diagPow_apply (n : ℕ) (a : Eˣ) (v : Fin n → E) (i : Fin n) :
    diagPow n a v i = (a : E) ^ (i : ℕ) * v i := by
  simp [diagPow, LinearEquiv.smulOfUnit, Units.smul_def]

variable (q) in
/-- **`Sp(n)` is isomorphic to its rescaling** by any unit `a`, through
`diag(1, a, …, a^(n-1))`. -/
def specialRescaleIso (n : ℕ) (a : Eˣ) :
    Iso (special q n hdeg hq) ((special q n hdeg hq).rescale a) where
  toRepresentationEquiv := .mk (diagPow n a) fun w ↦ by
    refine LinearMap.ext fun v ↦ funext fun i ↦ ?_
    simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply, diagPow_apply,
      rescale_r, special_r_apply]
    ring
  comp_N := by
    refine LinearMap.ext fun v ↦ funext fun i ↦ ?_
    simp only [LinearMap.comp_apply, Representation.Equiv.toLinearMap_mk', LinearEquiv.coe_coe,
      rescale_N, special_N, LinearMap.smul_apply, Pi.smul_apply, smul_eq_mul]
    rw [diagPow_apply, finShift_apply, finShift_apply]
    split_ifs with h
    · simp
    · rw [diagPow_apply, ← mul_assoc, ← pow_succ']
      congr 2
      dsimp only
      omega

@[simp]
theorem specialRescaleIso_apply (n : ℕ) (a : Eˣ) (v : Fin n → E) (i : Fin n) :
    specialRescaleIso q hdeg hq n a v i = (a : E) ^ (i : ℕ) * v i :=
  diagPow_apply n a v i

end WeilDeligneParameter

end TauCeti
