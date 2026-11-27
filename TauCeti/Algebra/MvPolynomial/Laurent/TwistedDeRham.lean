/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.MvPolynomial.Laurent.EulerDerivation
public import TauCeti.Algebra.MvPolynomial.Laurent.NewtonPolytope
import Mathlib.Data.Finset.CastCard

/-!
# The Newton filtration of the twisted de Rham complex of a torus

Let `φ` be a Laurent polynomial in the variables `K`. The twisted de Rham complex
`(Ω^•(T), d + dφ ∧)` of the torus `T = G_m^K` is written in the basis
`dlog x_J = dlog x_{j₁} ∧ ⋯ ∧ dlog x_{j_q}`: a form is a family `ω : Finset K → R[x^{±1}]` of
Laurent polynomials, and the differential is the Koszul differential
`TauCeti.koszulCochainDifferential (twistedEuler φ)` of the twisted Euler operators
`θ_i + θ_i(φ)`, where `θ_i = x_i ∂/∂x_i` (see
`TauCeti.Algebra.MvPolynomial.Laurent.EulerDerivation`).

The Newton filtration `F_a` of the Laurent ring (`TauCeti.LaurentRing.newtonFiltration`) is the
span of the monomials `x^m` with `m` in the cone over the Newton polytope `Δ(φ)` and Newton height
`h(m) ≤ a`. It induces the decreasing **Newton filtration of the twisted de Rham complex**,
indexed by a real number `c` (`TauCeti.LaurentRing.newtonFormFiltration`): `F^c` consists of the
forms `∑_J ω_J dlog x_J` with `ω_J ∈ F_{#J - c}` for every `J`. In degree `q` it vanishes for
`q < c` and is otherwise spanned by the forms `x^m dlog x_J` with `#J = q`, `m` in the cone and
`h(m) ≤ q - c`.

The Euler derivations act diagonally on monomials, so they preserve each `F_a`, and every exponent
of `φ` has height at most `1`, so `θ_i(φ) ∈ F_1`. Hence each twisted Euler operator maps `F_a` into
`F_{a+1}` (`TauCeti.LaurentRing.twistedEuler_mem_newtonFiltration`), and the twisted de Rham
differential `d + dφ ∧`, which raises the form degree by one, preserves every `F^c`
(`TauCeti.LaurentRing.koszulCochainDifferential_twistedEuler_mem_newtonFormFiltration`): the
`F^c` are subcomplexes. The untwisted part `d` of the differential even maps `F^c` into `F^{c+1}`,
so on the associated graded complex the differential is the Koszul differential of the
multiplications by the logarithmic derivatives `θ_i(φ)`
(`TauCeti.LaurentRing.koszulCochainDifferential_twistedEuler_sub_mem_newtonFormFiltration`). This
is the complex whose cohomology Kouchnirenko's graded acyclicity theorem computes. For finitely
many variables the filtration exhausts the forms with coefficients in the cone algebra
(`TauCeti.LaurentRing.iSup_newtonFormFiltration`).

## Main definitions

* `TauCeti.LaurentRing.newtonFormFiltration φ c`: the forms whose coefficient on `dlog x_J` lies
  in the Newton filtration step `F_{#J - c}`.

## Main results

* `TauCeti.LaurentRing.eulerDerivation_mem_newtonFiltration`: `θ_i F_a ⊆ F_a`.
* `TauCeti.LaurentRing.twistedEuler_mem_newtonFiltration`: `(θ_i + θ_i(φ)) F_a ⊆ F_{a+1}`.
* `TauCeti.LaurentRing.pi_single_single_mem_newtonFormFiltration_iff`: `x^m dlog x_J` lies in
  `F^c` exactly when `c ≤ #J`, `m` lies in the cone and `h(m) ≤ #J - c`.
* `TauCeti.LaurentRing.koszulCochainDifferential_twistedEuler_mem_newtonFormFiltration`:
  `d + dφ ∧` preserves `F^c`.
* `TauCeti.LaurentRing.koszulCochainDifferential_twistedEuler_sub_mem_newtonFormFiltration`:
  modulo `F^{c+1}`, `d + dφ ∧` agrees on `F^c` with `dφ ∧`.
* `TauCeti.LaurentRing.iSup_newtonFormFiltration`: the filtration exhausts the forms with
  coefficients in the cone algebra.

## References

* A. G. Kouchnirenko, *Polyèdres de Newton et nombres de Milnor*, Invent. Math. 32 (1976), §2.
* A. Adolphson and S. Sperber, *On twisted de Rham cohomology*, Nagoya Math. J. 146 (1997), §4,
  for the filtration of the twisted de Rham complex by the weight function of the Newton polytope.
* J.-D. Yu, *Irregular Hodge filtration on twisted de Rham cohomology*, Manuscripta Math. 144
  (2014), §4(a), (24)–(25), for the Newton filtration of the twisted de Rham complex.
-/

public section

open AddMonoidAlgebra Finset

namespace TauCeti.LaurentRing

variable {R K : Type*} [CommRing R] {φ f : LaurentRing R K} {a c : ℝ}

/-! ### The Euler operators and the Newton filtration of the Laurent ring -/

/-- The Euler derivation `θ_i` preserves each step `F_a` of the Newton filtration, since it
multiplies every monomial by a scalar. -/
theorem eulerDerivation_mem_newtonFiltration (i : K) (hf : f ∈ newtonFiltration φ a) :
    eulerDerivation i f ∈ newtonFiltration φ a := by
  rw [mem_newtonFiltration_iff] at hf ⊢
  refine fun m hm ↦ hf m (Finsupp.mem_support_iff.2 fun h ↦ Finsupp.mem_support_iff.1 hm ?_)
  rw [coeff_eulerDerivation, h, mul_zero]

/-- The logarithmic derivative `θ_i(φ)` of `φ` lies in `F_1`. -/
theorem eulerDerivation_self_mem_newtonFiltration_one (φ : LaurentRing R K) (i : K) :
    eulerDerivation i φ ∈ newtonFiltration φ 1 :=
  eulerDerivation_mem_newtonFiltration i (self_mem_newtonFiltration_one φ)

/-- The twisted Euler operator `θ_i + θ_i(φ)` raises the Newton filtration by one:
it maps `F_a` into `F_{a+1}`. -/
theorem twistedEuler_mem_newtonFiltration (i : K) (hf : f ∈ newtonFiltration φ a) :
    twistedEuler φ i f ∈ newtonFiltration φ (a + 1) := by
  rw [twistedEuler_apply]
  refine add_mem (newtonFiltration_mono φ (by linarith)
    (eulerDerivation_mem_newtonFiltration i hf)) ?_
  rw [add_comm a]
  exact mul_mem_newtonFiltration (eulerDerivation_self_mem_newtonFiltration_one φ i) hf

/-! ### The Newton filtration of the twisted de Rham complex -/

/-- The **Newton filtration of the twisted de Rham complex** of the torus: for real `c`, the
forms `∑_J ω_J dlog x_J`, written as families `ω : Finset K → LaurentRing R K`, whose coefficient
`ω_J` lies in the Newton filtration step `F_{#J - c}` for every `J`. It is decreasing in `c`, and
the twisted de Rham differential preserves it. -/
noncomputable def newtonFormFiltration (φ : LaurentRing R K) (c : ℝ) :
    Submodule R (Finset K → LaurentRing R K) :=
  Submodule.pi Set.univ fun J ↦ newtonFiltration φ (#J - c)

theorem newtonFormFiltration_def (φ : LaurentRing R K) (c : ℝ) :
    newtonFormFiltration φ c = Submodule.pi Set.univ fun J ↦ newtonFiltration φ (#J - c) :=
  (rfl)

variable {ω : Finset K → LaurentRing R K}

@[simp]
theorem mem_newtonFormFiltration_iff :
    ω ∈ newtonFormFiltration φ c ↔ ∀ J, ω J ∈ newtonFiltration φ (#J - c) := by
  simp [newtonFormFiltration_def]

/-- The Newton filtration of the twisted de Rham complex is decreasing. -/
theorem newtonFormFiltration_antitone (φ : LaurentRing R K) :
    Antitone (newtonFormFiltration φ) :=
  fun _ _ h ↦ Submodule.pi_mono fun _ _ ↦ newtonFiltration_mono φ (by linarith)

/-- The forms in `F^c` have no component of degree less than `c`. -/
theorem apply_eq_zero_of_mem_newtonFormFiltration (hω : ω ∈ newtonFormFiltration φ c)
    {J : Finset K} (hJ : (#J : ℝ) < c) : ω J = 0 := by
  have h := mem_newtonFormFiltration_iff.1 hω J
  rwa [newtonFiltration_eq_bot_of_neg (by linarith), Submodule.mem_bot] at h

/-- The form `f dlog x_J` lies in `F^c` exactly when `f` lies in `F_{#J - c}`. -/
theorem pi_single_mem_newtonFormFiltration_iff [DecidableEq K] {J : Finset K}
    {f : LaurentRing R K} :
    Pi.single J f ∈ newtonFormFiltration φ c ↔ f ∈ newtonFiltration φ (#J - c) := by
  refine ⟨fun h ↦ by simpa using mem_newtonFormFiltration_iff.1 h J, fun h ↦ ?_⟩
  refine mem_newtonFormFiltration_iff.2 fun I ↦ ?_
  rcases eq_or_ne I J with rfl | hI
  · simpa using h
  · simp [hI]

/-- The monomial form `r x^m dlog x_J` with `r ≠ 0` lies in `F^c` exactly when `c ≤ #J`, the
exponent `m` lies in the cone over the Newton polytope, and its Newton height is at most
`#J - c`. -/
theorem pi_single_single_mem_newtonFormFiltration_iff [DecidableEq K] {J : Finset K}
    {m : K →₀ ℤ} {r : R} (hr : r ≠ 0) :
    Pi.single J (single m r) ∈ newtonFormFiltration φ c ↔
      c ≤ #J ∧ latticePoint m ∈ ConvexCone.hull ℝ (newtonPolytope φ) ∧
        gauge (newtonPolytope φ) (latticePoint m) ≤ #J - c := by
  rw [pi_single_mem_newtonFormFiltration_iff, single_mem_newtonFiltration_iff hr]
  refine ⟨fun h ↦ ⟨?_, h⟩, fun h ↦ h.2⟩
  linarith [(gauge_nonneg (latticePoint m)).trans h.2]

/-- For finitely many variables, the Newton filtration of the twisted de Rham complex exhausts
the forms whose coefficients lie in the cone algebra, spanned by the monomials with exponent in
the cone over the Newton polytope. -/
theorem iSup_newtonFormFiltration [Finite K] (φ : LaurentRing R K) :
    ⨆ c, newtonFormFiltration φ c = Submodule.pi Set.univ fun _ ↦
      supported R R {m | latticePoint m ∈ ConvexCone.hull ℝ (newtonPolytope φ)} := by
  have : Fintype (Finset K) := Fintype.ofFinite _
  refine le_antisymm (iSup_le fun c ↦ Submodule.pi_mono fun J _ ↦
    (le_iSup (newtonFiltration φ) _).trans (iSup_newtonFiltration φ).le) fun ω hω ↦ ?_
  -- each coefficient lies in some step of the filtration, and there are finitely many of them
  have h (J : Finset K) : ∃ a, ω J ∈ newtonFiltration φ a :=
    (Submodule.mem_iSup_of_directed _ (newtonFiltration_mono φ).directed_le).1
      ((iSup_newtonFiltration φ).ge (hω J trivial))
  choose b hb using h
  refine Submodule.mem_iSup_of_mem (-∑ J, |b J|) (mem_newtonFormFiltration_iff.2 fun J ↦ ?_)
  refine newtonFiltration_mono φ ?_ (hb J)
  have := single_le_sum (f := fun J ↦ |b J|) (fun _ _ ↦ abs_nonneg _) (mem_univ J)
  linarith [le_abs_self (b J), (#J).cast_nonneg (α := ℝ)]

/-! ### The twisted de Rham differential preserves the Newton filtration -/

variable [LinearOrder K]

/-- **The twisted de Rham differential `d + dφ ∧` preserves the Newton filtration**: each `F^c`
is a subcomplex of the twisted de Rham complex of the torus. -/
theorem koszulCochainDifferential_twistedEuler_mem_newtonFormFiltration
    (hω : ω ∈ newtonFormFiltration φ c) :
    koszulCochainDifferential (twistedEuler φ) ω ∈ newtonFormFiltration φ c := by
  refine koszulCochainDifferential_mem_pi _ (fun J j hj f hf ↦ ?_) hω
  convert twistedEuler_mem_newtonFiltration j hf using 2
  rw [cast_card_erase_of_mem hj]
  ring

/-- The untwisted de Rham differential `d`, the Koszul differential of the Euler derivations,
maps `F^c` into `F^{c+1}`. -/
theorem koszulCochainDifferential_eulerDerivation_mem_newtonFormFiltration
    (hω : ω ∈ newtonFormFiltration φ c) :
    koszulCochainDifferential
        (fun i ↦ (eulerDerivation (R := R) i : Module.End R (LaurentRing R K))) ω ∈
      newtonFormFiltration φ (c + 1) := by
  refine koszulCochainDifferential_mem_pi _ (fun J j hj f hf ↦ ?_) hω
  convert eulerDerivation_mem_newtonFiltration j hf using 2
  rw [cast_card_erase_of_mem hj]
  ring

/-- The Koszul differential `dφ ∧` of the multiplications by the logarithmic derivatives
`θ_i(φ)` preserves the Newton filtration. -/
theorem koszulCochainDifferential_mulLeft_mem_newtonFormFiltration
    (hω : ω ∈ newtonFormFiltration φ c) :
    koszulCochainDifferential (fun i ↦ LinearMap.mulLeft R (eulerDerivation i φ)) ω ∈
      newtonFormFiltration φ c := by
  refine koszulCochainDifferential_mem_pi _ (fun J j hj f hf ↦ ?_) hω
  rw [LinearMap.mulLeft_apply]
  convert mul_mem_newtonFiltration (eulerDerivation_self_mem_newtonFiltration_one φ j) hf using 2
  rw [cast_card_erase_of_mem hj]
  ring

/-- **The graded twisted de Rham differential.** On `F^c`, the twisted de Rham differential
`d + dφ ∧` agrees modulo `F^{c+1}` with the Koszul differential `dφ ∧` of the multiplications by
the logarithmic derivatives `θ_i(φ)`. Hence on the associated graded complex of the Newton
filtration the differential is induced by multiplication by the `θ_i(φ)`. -/
theorem koszulCochainDifferential_twistedEuler_sub_mem_newtonFormFiltration
    (hω : ω ∈ newtonFormFiltration φ c) :
    koszulCochainDifferential (twistedEuler φ) ω -
        koszulCochainDifferential (fun i ↦ LinearMap.mulLeft R (eulerDerivation i φ)) ω ∈
      newtonFormFiltration φ (c + 1) := by
  have h : twistedEuler φ =
      (fun i ↦ (eulerDerivation (R := R) i : Module.End R (LaurentRing R K))) +
        fun i ↦ LinearMap.mulLeft R (eulerDerivation i φ) :=
    funext fun i ↦ LinearMap.ext fun g ↦ by simp
  rw [h, koszulCochainDifferential_add, LinearMap.add_apply, add_sub_cancel_right]
  exact koszulCochainDifferential_eulerDerivation_mem_newtonFormFiltration hω

end TauCeti.LaurentRing
