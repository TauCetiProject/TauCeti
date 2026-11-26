/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.WeilDeligne.Special

import TauCeti.LinearAlgebra.Monomial

/-!
# Rescaling the monodromy of a Weil–Deligne parameter

For a raw Weil–Deligne parameter `(V, r, N)` and a scalar `a`, the pair `(r, a N)` is again a
raw Weil–Deligne parameter (`TauCeti.WeilDeligneParameter.rescale`): `a N` is nilpotent and
satisfies the same conjugation relation. Rescaling is functorial in morphisms and isomorphisms,
composes multiplicatively, and commutes with transport and with twists by characters.

For `q ≥ 2` and finite inertia image, `(r, N) ≅ (r, a N)` for every `a ≠ 0` (Deligne 1973, proof
of §8.4.3). This file proves it for the special parameters `Sp(n)`, where the diagonal matrix
`diag(1, a, …, a^(n-1))` commutes with the Weil action and conjugates `N` to `a N`
(`TauCeti.WeilDeligneParameter.specialRescaleIso`). The hypothesis `q ≥ 2` is needed in general:
if some `r(w)` equals `1 + N`, as happens for `q = 1`, then every automorphism commuting with the
Weil action commutes with `N`, so a nonzero `N` is isomorphic to its rescaling by `a` only for
`a = 1` (`TauCeti.WeilDeligneParameter.eq_one_of_iso_rescale`).

## Main definitions

* `TauCeti.WeilDeligneParameter.rescale`: the parameter `(r, a N)`.
* `TauCeti.WeilDeligneParameter.Hom.rescale`: rescaling a morphism.
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

variable {E W V V' V'' : Type*} [Field E] [Group W] [TopologicalSpace W]
  [AddCommGroup V] [Module E V] [AddCommGroup V'] [Module E V'] [AddCommGroup V''] [Module E V'']
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

/-- Rescaling twice multiplies the scalars. -/
@[simp]
theorem rescale_rescale (D : WeilDeligneParameter E W V deg q) (a b : E) :
    (D.rescale a).rescale b = D.rescale (b * a) := by
  ext1 <;> simp [mul_smul]

/-- Rescaling commutes with transport. -/
theorem rescale_transport (D : WeilDeligneParameter E W V deg q) (e : V ≃ₗ[E] V') (a : E) :
    (D.transport e).rescale a = (D.rescale a).transport e := by
  ext w v <;> simp [transport_r_apply, transport_N_apply]

/-- Rescaling commutes with twisting by a character. -/
theorem rescale_twist [SeparatelyContinuousMul W] (D : WeilDeligneParameter E W V deg q)
    (χ : W →* Eˣ) (hχ : IsOpen (χ.ker : Set W)) (a : E) :
    (D.twist χ hχ).rescale a = (D.rescale a).twist χ hχ := by
  ext1 <;> simp

section Functoriality

variable {D : WeilDeligneParameter E W V deg q} {D' : WeilDeligneParameter E W V' deg q}
  {D'' : WeilDeligneParameter E W V'' deg q} (a : E)

/-- A morphism of parameters is also a morphism of their rescalings. -/
def Hom.rescale (f : Hom D D') : Hom (D.rescale a) (D'.rescale a) where
  toIntertwiningMap := f.toIntertwiningMap
  comp_N := by
    rw [rescale_N, rescale_N, LinearMap.comp_smul, LinearMap.smul_comp]
    exact congrArg (a • ·) f.comp_N

@[simp]
theorem Hom.rescale_apply (f : Hom D D') (v : V) : f.rescale a v = f v :=
  (rfl)

@[simp]
theorem Hom.rescale_id : (Hom.id D).rescale a = Hom.id (D.rescale a) :=
  Hom.ext (LinearMap.ext fun v ↦ by simp)

@[simp]
theorem Hom.rescale_comp (f : Hom D' D'') (g : Hom D D') :
    (f.comp g).rescale a = (f.rescale a).comp (g.rescale a) :=
  Hom.ext (LinearMap.ext fun v ↦ by simp)

/-- An isomorphism of parameters is also an isomorphism of their rescalings. -/
def Iso.rescale (f : Iso D D') : Iso (D.rescale a) (D'.rescale a) :=
  Iso.ofBijective (f.toHom.rescale a) (by
    rw [show ⇑(f.toHom.rescale a) = f from funext fun v ↦ by simp]
    exact f.bijective)

@[simp]
theorem Iso.coe_rescale (f : Iso D D') : ⇑(f.rescale a) = f :=
  funext fun v ↦ by simp [Iso.rescale]

@[simp]
theorem Iso.toHom_rescale (f : Iso D D') : (f.rescale a).toHom = f.toHom.rescale a :=
  Hom.ext (LinearMap.ext fun v ↦ by simp)

@[simp]
theorem Iso.rescale_refl : (Iso.refl D).rescale a = Iso.refl (D.rescale a) :=
  Iso.ext (LinearEquiv.ext fun v ↦ by simp)

@[simp]
theorem Iso.rescale_trans (f : Iso D D') (g : Iso D' D'') :
    (f.trans g).rescale a = (f.rescale a).trans (g.rescale a) :=
  Iso.ext (LinearEquiv.ext fun v ↦ by simp)

@[simp]
theorem Iso.rescale_symm (f : Iso D D') : (f.rescale a).symm = f.symm.rescale a :=
  Iso.ext (LinearEquiv.ext fun v ↦ (f.rescale a).injective (by simp))

end Functoriality

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
    (hcomm v).symm.trans (by rw [f.map_N_apply, rescale_N, LinearMap.smul_apply])
  by_contra ha
  refine hN (LinearMap.ext fun v ↦ ?_)
  obtain ⟨u, rfl⟩ := EquivLike.surjective f v
  have h : (a - 1) • D.N (f u) = 0 := by rw [sub_smul, one_smul, ← hscale u, sub_self]
  rw [LinearMap.zero_apply]
  exact (smul_eq_zero.mp h).resolve_left (sub_ne_zero.mpr ha)

/-! ### Rescaling the special parameters -/

variable (hdeg : Continuous deg) (hq : (q : E) ≠ 0)

variable (q) in
/-- **`Sp(n)` is isomorphic to its rescaling** by any unit `a`, through
`diag(1, a, …, a^(n-1))`. -/
def specialRescaleIso (n : ℕ) (a : Eˣ) :
    Iso (special q n hdeg hq) ((special q n hdeg hq).rescale a) where
  toRepresentationEquiv := .mk (monomialEquiv (fun i : Fin n ↦ a ^ (i : ℕ)) (.refl _)) fun w ↦ by
    refine LinearMap.ext fun v ↦ funext fun i ↦ ?_
    simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply, monomialEquiv_apply,
      Equiv.refl_symm, Equiv.refl_apply, rescale_r, special_r_apply]
    ring
  comp_N := by
    refine LinearMap.ext fun v ↦ funext fun i ↦ ?_
    simp only [LinearMap.comp_apply, Representation.Equiv.toLinearMap_mk', LinearEquiv.coe_coe,
      rescale_N, special_N, LinearMap.smul_apply, Pi.smul_apply, smul_eq_mul]
    simp only [monomialEquiv_apply, Equiv.refl_symm, Equiv.refl_apply, Units.val_pow_eq_pow_val,
      finShift_apply]
    split_ifs with h
    · simp
    · rw [← mul_assoc, ← pow_succ']
      congr 2
      omega

@[simp]
theorem specialRescaleIso_apply (n : ℕ) (a : Eˣ) (v : Fin n → E) (i : Fin n) :
    specialRescaleIso q hdeg hq n a v i = (a : E) ^ (i : ℕ) * v i := by
  simp [specialRescaleIso]

end WeilDeligneParameter

end TauCeti
