/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.AdicCompletion.Pi
public import TauCeti.RingTheory.Perfection.MapEquiv
public import TauCeti.RingTheory.Perfection.Pi
public import TauCeti.RingTheory.Perfectoid.PreTilt.Map
public import TauCeti.RingTheory.WittVector.MapEquiv
public import TauCeti.RingTheory.WittVector.Pi

import TauCeti.RingTheory.Ideal.IsPrincipal

/-!
# Tilts and `A_inf` of products

Let `(A i)` be an arbitrary family of commutative rings. Reduction modulo `p` commutes with the
product, `(∏ A i) ⧸ p ≅ ∏ (A i ⧸ p)`, because the ideal `p (∏ A i)` consists of the families of
multiples of `p`. Perfections are computed coordinatewise (`Perfection.piEquiv`), so the
projections induce an isomorphism of tilts `(∏ A i)♭ ≅ ∏ (A i)♭`. Witt vectors are computed
coordinatewise as well, so `W(∏ R i) ≅ ∏ W(R i)` for any family of rings, and together these give
`A_inf(∏ A i) ≅ ∏ A_inf(A i)`, where `A_inf(A) = W(A♭)`.

When every `A i` is `p`-adically complete, so is the product
(`IsAdicComplete.pi_span_natCast`), and the isomorphisms above are compatible with the sharp maps
and with Fontaine's maps `θ`: the sharp of a family of compatible root systems is the family of
the sharps, and `θ` of the product is the product of the `θ`s. So `ker θ` of the product is the
product of the kernels, and it is principal exactly when every factor's kernel is. This is the
input, at the level of tilts and Fontaine's maps, for the stability of integral perfectoid rings
under products and fibre products.

No finiteness is assumed on the index type. The tilt of a ring is formed only when `p` is not a
unit in it; for the product this holds as soon as the family is nonempty and `p` is a nonunit in
every factor (`Pi.fact_not_isUnit_natCast`).

## Main definitions

* `ModP.piEquiv`: `ModP (∀ i, A i) p ≃+* ∀ i, ModP (A i) p`.
* `PreTilt.piEquiv`: `PreTilt (∀ i, A i) p ≃+* ∀ i, PreTilt (A i) p`, by the projections.
* `PreTilt.wittVectorPiEquiv`: `A_inf(∏ A i) ≃+* ∏ A_inf(A i)`.

## Main results

* `PreTilt.untilt_piEquiv_apply`, `PreTilt.untilt_piEquiv_symm`: the tilt isomorphism is
  compatible with the sharp maps.
* `PreTilt.fontaineTheta_wittVectorPiEquiv_apply`, `PreTilt.fontaineTheta_wittVectorPiEquiv_symm`:
  the `A_inf` isomorphism is compatible with Fontaine's maps.
* `PreTilt.map_wittVectorPiEquiv_ker_fontaineTheta`: the `A_inf` isomorphism carries `ker θ` of
  the product onto the product of the kernels.
* `PreTilt.isPrincipal_ker_fontaineTheta_pi_iff`: `ker θ` of the product is principal if and only
  if `ker θ` of every factor is (`Ideal.isPrincipal_pi_iff`).

## References

* K. Česnavičius, P. Scholze, *Purity for flat cohomology*, §2.1.1, p. 10.
-/

public section

open Ideal

variable {ι : Type*} {A : ι → Type*} [∀ i, CommRing (A i)]

namespace ModP

variable (p : ℕ)

/-- Reduction modulo `p` commutes with products: `(∀ i, A i) ⧸ p ≃+* ∀ i, A i ⧸ p`, by the
reductions of the projections. -/
noncomputable def piEquiv : ModP (∀ i, A i) p ≃+* ∀ i, ModP (A i) p :=
  RingEquiv.ofBijective (RingHom.pi fun i ↦ map p (Pi.evalRingHom A i)) <| by
    refine ⟨(injective_iff_map_eq_zero _).mpr fun x hx ↦ ?_, fun y ↦ ?_⟩
    · obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
      rw [Ideal.Quotient.eq_zero_iff_mem, mem_span_singleton, pi_dvd_iff]
      intro i
      simpa [Ideal.Quotient.eq_zero_iff_mem, mem_span_singleton] using congr_fun hx i
    · choose a ha using fun i ↦ Ideal.Quotient.mk_surjective (y i)
      refine ⟨Ideal.Quotient.mk _ a, funext fun i ↦ ?_⟩
      rw [RingHom.pi_apply, map_mk, Pi.evalRingHom_apply, ha]

@[simp]
theorem piEquiv_apply (x : ModP (∀ i, A i) p) (i : ι) :
    piEquiv p x i = map p (Pi.evalRingHom A i) x :=
  (rfl)

@[simp]
theorem piEquiv_mk (a : ∀ i, A i) :
    piEquiv p (Ideal.Quotient.mk _ a) = fun i ↦ Ideal.Quotient.mk _ (a i) :=
  funext fun i ↦ by simp

@[simp]
theorem piEquiv_symm_mk (a : ∀ i, A i) :
    (piEquiv p).symm (fun i ↦ Ideal.Quotient.mk _ (a i)) = Ideal.Quotient.mk _ a :=
  (piEquiv p).symm_apply_eq.mpr (piEquiv_mk p a).symm

end ModP

/-- A product of rings is a ring in which `p` is not a unit as soon as the family is nonempty and
`p` is not a unit in any factor. -/
instance Pi.fact_not_isUnit_natCast (p : ℕ) [Nonempty ι] [∀ i, Fact ¬IsUnit (p : A i)] :
    Fact ¬IsUnit (p : ∀ i, A i) :=
  ⟨fun h ↦ Fact.out (p := ¬IsUnit (p : A (Classical.arbitrary ι))) <|
    (Pi.isUnit_iff.mp h) (Classical.arbitrary ι)⟩

namespace PreTilt

variable (p : ℕ) [Fact p.Prime] [∀ i, Fact ¬IsUnit (p : A i)] [Fact ¬IsUnit (p : ∀ i, A i)]

/-- **The tilt of a product is the product of the tilts**: the projections induce a ring
isomorphism `(∏ A i)♭ ≃+* ∏ (A i)♭`, the perfection of `ModP.piEquiv` (`Perfection.mapEquiv`)
followed by `Perfection.piEquiv`. -/
noncomputable def piEquiv : PreTilt (∀ i, A i) p ≃+* ∀ i, PreTilt (A i) p :=
  -- `p` is a unit in the zero ring, so the family is nonempty
  haveI : Nonempty ι := not_isEmpty_iff.mp fun _ ↦
    Fact.out (p := ¬IsUnit (p : ∀ i, A i)) (isUnit_of_subsingleton _)
  equivPerfection.trans <| (Perfection.mapEquiv p (ModP.piEquiv p)).trans <|
    (Perfection.piEquiv p).trans <| RingEquiv.piCongrRight fun _ ↦ equivPerfection.symm

variable {p}

@[simp]
theorem piEquiv_apply (x : PreTilt (∀ i, A i) p) (i : ι) :
    piEquiv p x i = map p (Pi.evalRingHom A i) x :=
  ext fun n ↦ by simp [piEquiv]

/-- The coordinates of `(piEquiv p).symm y` are the families of coordinates of the `y i`. -/
@[simp]
theorem coeff_piEquiv_symm (y : ∀ i, PreTilt (A i) p) (n : ℕ) :
    coeff n ((piEquiv p).symm y) = (ModP.piEquiv p).symm fun i ↦ coeff n (y i) := by
  refine ((ModP.piEquiv (A := A) p).symm_apply_eq.mpr (funext fun i ↦ ?_)).symm
  rw [ModP.piEquiv_apply, ← coeff_map, ← piEquiv_apply, RingEquiv.apply_symm_apply]

variable [∀ i, IsAdicComplete (span {(p : A i)}) (A i)]

/-- The sharp of the `i`-th component of `x ∈ (∏ A j)♭` is the `i`-th component of `x♯`. -/
theorem untilt_piEquiv_apply (x : PreTilt (∀ i, A i) p) (i : ι) :
    (piEquiv p x i).untilt = x.untilt i := by
  rw [piEquiv_apply, untilt_natural, Pi.evalRingHom_apply]

/-- The sharp of the compatible system corresponding to a family `y` is the family of sharps. -/
@[simp]
theorem untilt_piEquiv_symm (y : ∀ i, PreTilt (A i) p) :
    ((piEquiv p).symm y).untilt = fun i ↦ (y i).untilt :=
  funext fun i ↦ by rw [← untilt_piEquiv_apply, RingEquiv.apply_symm_apply]

end PreTilt

namespace PreTilt

variable (p : ℕ) [Fact p.Prime] [∀ i, Fact ¬IsUnit (p : A i)] [Fact ¬IsUnit (p : ∀ i, A i)]

/-- **`A_inf` of a product is the product of the `A_inf`**: `W((∏ A i)♭) ≃+* ∏ W((A i)♭)`, the
Witt vectors of `PreTilt.piEquiv` (`WittVector.mapEquiv`) followed by `WittVector.piEquiv`. -/
noncomputable def wittVectorPiEquiv :
    WittVector p (PreTilt (∀ i, A i) p) ≃+* ∀ i, WittVector p (PreTilt (A i) p) :=
  (WittVector.mapEquiv (piEquiv p)).trans (WittVector.piEquiv p)

variable {p}

/-- The `i`-th component of `wittVectorPiEquiv p w` is `w` mapped along the tilt of the `i`-th
projection. -/
@[simp]
theorem wittVectorPiEquiv_apply (w : WittVector p (PreTilt (∀ i, A i) p)) (i : ι) :
    wittVectorPiEquiv p w i = WittVector.map (map p (Pi.evalRingHom A i)) w :=
  WittVector.ext fun n ↦ by simp [wittVectorPiEquiv, WittVector.map_coeff]

variable [∀ i, IsAdicComplete (span {(p : A i)}) (A i)]

/-- **Fontaine's map of a product**: `θ` of the `i`-th component of `wittVectorPiEquiv p w` is the
`i`-th component of `θ w`. -/
theorem fontaineTheta_wittVectorPiEquiv_apply (w : WittVector p (PreTilt (∀ i, A i) p)) (i : ι) :
    WittVector.fontaineTheta (A i) p (wittVectorPiEquiv p w i) =
      WittVector.fontaineTheta (∀ i, A i) p w i := by
  rw [wittVectorPiEquiv_apply, WittVector.theta_natural, Pi.evalRingHom_apply]

/-- **Fontaine's map of a product is the product of Fontaine's maps**: under
`A_inf(∏ A i) ≃+* ∏ A_inf(A i)`, `θ` of the product is computed componentwise. -/
@[simp]
theorem fontaineTheta_wittVectorPiEquiv_symm (v : ∀ i, WittVector p (PreTilt (A i) p)) :
    WittVector.fontaineTheta (∀ i, A i) p ((wittVectorPiEquiv p).symm v) =
      fun i ↦ WittVector.fontaineTheta (A i) p (v i) :=
  funext fun i ↦ by rw [← fontaineTheta_wittVectorPiEquiv_apply, RingEquiv.apply_symm_apply]

/-- **The kernel of Fontaine's map of a product is the product of the kernels**: under
`A_inf(∏ A i) ≃+* ∏ A_inf(A i)`, `ker θ` corresponds to `∏ ker θ_i`. -/
theorem map_wittVectorPiEquiv_ker_fontaineTheta :
    (RingHom.ker (WittVector.fontaineTheta (∀ i, A i) p)).map (wittVectorPiEquiv p) =
      Ideal.pi fun i ↦ RingHom.ker (WittVector.fontaineTheta (A i) p) := by
  ext v
  rw [← comap_symm, mem_comap, RingHom.mem_ker, fontaineTheta_wittVectorPiEquiv_symm, mem_pi,
    funext_iff]
  simp [RingHom.mem_ker]

/-- The kernel of Fontaine's map of a product is principal exactly when the kernel of Fontaine's
map of every factor is principal. -/
theorem isPrincipal_ker_fontaineTheta_pi_iff :
    (RingHom.ker (WittVector.fontaineTheta (∀ i, A i) p)).IsPrincipal ↔
      ∀ i, (RingHom.ker (WittVector.fontaineTheta (A i) p)).IsPrincipal := by
  rw [← isPrincipal_pi_iff, ← map_wittVectorPiEquiv_ker_fontaineTheta]
  -- principality is preserved by the ring isomorphism `wittVectorPiEquiv` and by its inverse
  refine ⟨fun h ↦ h.map_ringHom _, fun h ↦ ?_⟩
  simpa only [map_symm, comap_map_of_bijective _ (wittVectorPiEquiv p).bijective] using
    h.map_ringHom (wittVectorPiEquiv p).symm

end PreTilt
