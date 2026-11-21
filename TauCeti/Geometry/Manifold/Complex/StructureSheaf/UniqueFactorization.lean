/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.UniqueFactorizationDomain.Basic
public import TauCeti.Geometry.Manifold.Complex.StructureSheaf.Domain
public import TauCeti.Geometry.Manifold.Complex.StructureSheaf.SmoothComparison
public import TauCeti.Geometry.Manifold.Complex.StructureSheaf.Weierstrass

import TauCeti.Geometry.Manifold.Complex.StructureSheaf.Rueckert
import TauCeti.Geometry.Manifold.Complex.StructureSheaf.StalkPullback

/-!
# Holomorphic stalks are unique factorisation domains

The ring `𝒪_{X, x}` of germs of holomorphic functions at a point of a finite-dimensional complex
manifold without boundary is a unique factorisation domain.

The proof follows Rückert's inductive descent along Weierstrass preparation and division. In
dimension zero the stalk is `ℂ`. For the inductive step from `Fin n → ℂ` to `(Fin n → ℂ) × ℂ` at
`(0, 0)`, vertical polynomial evaluation satisfies the Rückert hypotheses with respect to
distinguished polynomials (`TauCeti.holomorphicStructureSheaf.isRueckert_evalVertical`), and
Rückert's factorial descent (`RingHom.IsRueckert.uniqueFactorizationMonoid`) passes unique
factorisation from `𝒪_{Fin n → ℂ, 0}` to `𝒪_{(Fin n → ℂ) × ℂ, (0, 0)}`. Dimension induction and
chart pullback (`TauCeti.holomorphicStructureSheaf.stalk_induction`) then transfer the property to
arbitrary finite-dimensional complex manifolds without boundary, as well as to Mathlib's native
complex-smooth structure sheaf via `TauCeti.holomorphicStructureSheaf.smoothStalkIso`.

As immediate consequences of the Rückert hypotheses and factoriality, a distinguished polynomial
`P ∈ (𝒪_{E, x₀})[X]` generates a prime ideal, is prime, or is irreducible in `(𝒪_{E, x₀})[X]` if
and only if `evalVertical x₀ w₀ P` has the corresponding property in `𝒪_{E × ℂ, (x₀, w₀)}`, and the
same holds for any germ admitting `P` as its Weierstrass polynomial.

## Main declarations

* `TauCeti.holomorphicStructureSheaf.stalkUniqueFactorizationMonoid`: holomorphic stalks are
  unique factorisation domains.
* `TauCeti.holomorphicStructureSheaf.smoothStalkUniqueFactorizationMonoid`: so are the stalks of
  Mathlib's complex-smooth structure sheaf.
* `TauCeti.holomorphicStructureSheaf.isPrime_span_evalVertical_iff_of_isDistinguishedAt`,
  `TauCeti.holomorphicStructureSheaf.prime_evalVertical_iff_of_isDistinguishedAt`,
  `TauCeti.holomorphicStructureSheaf.irreducible_evalVertical_iff_of_isDistinguishedAt`:
  primality and irreducibility of a distinguished polynomial agree in `(𝒪_{E, x₀})[X]` and in
  `𝒪_{E × ℂ, (x₀, w₀)}`.
* `TauCeti.holomorphicStructureSheaf.prime_iff_of_weierstrassPreparation`,
  `TauCeti.holomorphicStructureSheaf.irreducible_iff_of_weierstrassPreparation`: the same
  comparison for any Weierstrass factorization `f = evalVertical x₀ w₀ P * u`.

## References

* J.-P. Demailly, *Complex Analytic and Differential Geometry*, Chapter II, Theorem (2.10).
* R. C. Gunning and H. Rossi, *Analytic Functions of Several Complex Variables*, Ch. II, §B.
* L. Hörmander, *An Introduction to Complex Analysis in Several Variables*, §6.1.
* S. Bosch, U. Güntzer and R. Remmert, *Non-Archimedean Analysis*, §5.2.5 (for Rückert descent).
-/

public noncomputable section

open Polynomial
open scoped ContDiff Manifold

namespace TauCeti.holomorphicStructureSheaf

section Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℂ E H} [I.Boundaryless]
  {X : Type} [TopologicalSpace X] [ChartedSpace H X] [IsManifold I 1 X]

/-- The stalk of holomorphic functions at any point of a finite-dimensional complex manifold
without boundary is a unique factorisation domain. -/
instance stalkUniqueFactorizationMonoid (x : X) :
    UniqueFactorizationMonoid ((holomorphicStructureSheaf I X).presheaf.stalk x) :=
  stalk_induction (fun R _ ↦ UniqueFactorizationMonoid R)
    (fun e h ↦ e.toMulEquiv.uniqueFactorizationMonoid h) inferInstance
    (fun n hV ↦ have := hV 0
      (isRueckert_evalVertical (0 : Fin n → ℂ) 0).uniqueFactorizationMonoid) x

/-- A stalk of Mathlib's complex-smooth structure sheaf on a finite-dimensional complex manifold
without boundary is a unique factorisation domain, via its comparison with holomorphic germs. -/
instance smoothStalkUniqueFactorizationMonoid (x : X) :
    UniqueFactorizationMonoid ((smoothSheafCommRing I 𝓘(ℂ) X ℂ).presheaf.stalk x) :=
  (smoothStalkIso I X x).commRingCatIsoToRingEquiv.toMulEquiv.uniqueFactorizationMonoid
    inferInstance

end Manifold

section Primality

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]

/-- A distinguished polynomial `P ∈ (𝒪_{E, x₀})[X]` generates a prime ideal after vertical
evaluation in `𝒪_{E × ℂ, (x₀, w₀)}` if and only if it generates a prime ideal in `(𝒪_{E, x₀})[X]`.
-/
theorem isPrime_span_evalVertical_iff_of_isDistinguishedAt {x₀ : E} {w₀ : ℂ}
    {P : ((holomorphicStructureSheaf 𝓘(ℂ, E) E).presheaf.stalk x₀)[X]}
    (hP : P.IsDistinguishedAt
      (IsLocalRing.maximalIdeal ((holomorphicStructureSheaf 𝓘(ℂ, E) E).presheaf.stalk x₀))) :
    (Ideal.span {evalVertical x₀ w₀ P}).IsPrime ↔ (Ideal.span {P}).IsPrime :=
  (isRueckert_evalVertical x₀ w₀).isPrime_span_apply_iff hP

/-- A distinguished polynomial `P ∈ (𝒪_{E, x₀})[X]` becomes a prime germ under vertical evaluation
if and only if it is prime in `(𝒪_{E, x₀})[X]`. -/
theorem prime_evalVertical_iff_of_isDistinguishedAt {x₀ : E} {w₀ : ℂ}
    {P : ((holomorphicStructureSheaf 𝓘(ℂ, E) E).presheaf.stalk x₀)[X]}
    (hP : P.IsDistinguishedAt
      (IsLocalRing.maximalIdeal ((holomorphicStructureSheaf 𝓘(ℂ, E) E).presheaf.stalk x₀))) :
    Prime (evalVertical x₀ w₀ P) ↔ Prime P :=
  (isRueckert_evalVertical x₀ w₀).prime_apply_iff hP

/-- For a Weierstrass factorization `f = evalVertical x₀ w₀ P * u`, the germ `f` is prime in
`𝒪_{E × ℂ, (x₀, w₀)}` if and only if the distinguished polynomial `P` is prime in
`(𝒪_{E, x₀})[X]`. -/
theorem prime_iff_of_weierstrassPreparation {x₀ : E} {w₀ : ℂ}
    {f u : (holomorphicStructureSheaf 𝓘(ℂ, E × ℂ) (E × ℂ)).presheaf.stalk (x₀, w₀)}
    {P : ((holomorphicStructureSheaf 𝓘(ℂ, E) E).presheaf.stalk x₀)[X]}
    (hP : P.IsDistinguishedAt
      (IsLocalRing.maximalIdeal ((holomorphicStructureSheaf 𝓘(ℂ, E) E).presheaf.stalk x₀)))
    (hu : IsUnit u) (hf : f = evalVertical x₀ w₀ P * u) :
    Prime f ↔ Prime P := by
  rw [hf, prime_mul_iff, or_iff_left (fun h ↦ h.2.not_isUnit hu),
    and_iff_left hu, prime_evalVertical_iff_of_isDistinguishedAt hP]

/-- A distinguished polynomial `P ∈ (𝒪_{E, x₀})[X]` is irreducible in `𝒪_{E × ℂ, (x₀, w₀)}` after
vertical evaluation if and only if it is irreducible in `(𝒪_{E, x₀})[X]`. -/
theorem irreducible_evalVertical_iff_of_isDistinguishedAt {x₀ : E} {w₀ : ℂ}
    {P : ((holomorphicStructureSheaf 𝓘(ℂ, E) E).presheaf.stalk x₀)[X]}
    (hP : P.IsDistinguishedAt
      (IsLocalRing.maximalIdeal ((holomorphicStructureSheaf 𝓘(ℂ, E) E).presheaf.stalk x₀))) :
    Irreducible (evalVertical x₀ w₀ P) ↔ Irreducible P :=
  (isRueckert_evalVertical x₀ w₀).irreducible_apply_iff hP

/-- For a Weierstrass factorization `f = evalVertical x₀ w₀ P * u`, the germ `f` is irreducible in
`𝒪_{E × ℂ, (x₀, w₀)}` if and only if its distinguished polynomial `P` is irreducible in
`(𝒪_{E, x₀})[X]`. -/
theorem irreducible_iff_of_weierstrassPreparation {x₀ : E} {w₀ : ℂ}
    {f u : (holomorphicStructureSheaf 𝓘(ℂ, E × ℂ) (E × ℂ)).presheaf.stalk (x₀, w₀)}
    {P : ((holomorphicStructureSheaf 𝓘(ℂ, E) E).presheaf.stalk x₀)[X]}
    (hP : P.IsDistinguishedAt
      (IsLocalRing.maximalIdeal ((holomorphicStructureSheaf 𝓘(ℂ, E) E).presheaf.stalk x₀)))
    (hu : IsUnit u) (hf : f = evalVertical x₀ w₀ P * u) :
    Irreducible f ↔ Irreducible P := by
  rw [UniqueFactorizationMonoid.irreducible_iff_prime,
    UniqueFactorizationMonoid.irreducible_iff_prime,
    prime_iff_of_weierstrassPreparation hP hu hf]

end Primality

end TauCeti.holomorphicStructureSheaf
