/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Rigid.Affinoid.Presheaf
public import TauCeti.RingTheory.Affinoid.Subdomain.Laurent
public import TauCeti.RingTheory.Affinoid.Subdomain.Rational.Basic

import TauCeti.RingTheory.Affinoid.QuotientNorm

/-!
# Idempotent, rational, and Laurent affinoid subdomains

This file wraps the algebraic idempotent, rational-domain, and Laurent-domain representation
theorems as constructors of `TauCeti.AffinoidSubdomain`, requiring only algebraic affinoidness
(with no chosen norm on the ambient algebra):

* `TauCeti.AffinoidSubdomain.ofIsIdempotentElem`: clopen Zariski domains `D(e)` for idempotents
  `e ∈ A` (over any complete ultrametric field `K`).
* `TauCeti.AffinoidSubdomain.rational`: rational domains `R(f/g)` when `(g, f₁, …, fₘ) = ⊤`.
* `TauCeti.AffinoidSubdomain.laurent`: Laurent domains `L(f, g⁻¹)`.
* `TauCeti.AffinoidSubdomain.eqOne`: unit-sphere loci `{x ∈ Sp A : |f(x)| = 1}`.
* `TauCeti.AffinoidSubdomain.closedSublevelPow`: closed rational sublevel domains
  `R(fⁿ / ϖ) = {x ∈ Sp A : |f(x)|ⁿ ≤ ‖ϖ‖}` for `ϖ ≠ 0`.

## References

* [Bosch, Güntzer, Remmert, *Non-Archimedean Analysis*][bosch-guntzer-remmert], §§7.2.2 and
  7.2.3.
-/

public section

namespace TauCeti.AffinoidSubdomain

universe u

section Idempotent

variable {K : Type*} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A : Type u} [CommRing A] [Algebra K A]

/-- The clopen affinoid subdomain `D(e)` associated to an idempotent `e ∈ A`. -/
def ofIsIdempotentElem (hA : IsAffinoidAlgebra K A) {e : A}
    (he : IsIdempotentElem e) : AffinoidSubdomain K A :=
  ofMap (IsAffinoidSubdomainMap.quotient_one_sub_of_isIdempotentElem hA he)

@[simp]
theorem coe_ofIsIdempotentElem (hA : IsAffinoidAlgebra K A) {e : A}
    (he : IsIdempotentElem e) :
    (ofIsIdempotentElem hA he : Set (MaximalSpectrum A)) =
      MaximalSpectrum.basicOpen e :=
  coe_ofMap _

end Idempotent

section RationalLaurent

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A : Type u} [CommRing A] [Algebra K A]

/-- Any rational domain `R(f/g)` with `Ideal.span (insert g (Set.range f)) = ⊤` is an affinoid
subdomain of `Sp A`, with no chosen norm on `A`. -/
noncomputable def rational (hA : IsAffinoidAlgebra K A) {m : ℕ} {g : A} {f : Fin m → A}
    (h : Ideal.span (insert g (Set.range f)) = ⊤) : AffinoidSubdomain K A :=
  let _ := hA.residueNormedCommRing; let _ := hA.residueNormedAlgebra
  have := hA.isUltrametricDist_residueNormedCommRing; have := hA.completeSpace_residueNormedCommRing
  ofMap (RationalFraction.isAffinoidSubdomainMap hA h)

@[simp]
theorem coe_rational (hA : IsAffinoidAlgebra K A) {m : ℕ} {g : A} {f : Fin m → A}
    (h : Ideal.span (insert g (Set.range f)) = ⊤) :
    (rational hA h : Set (MaximalSpectrum A)) = rationalDomain K g f := by
  let _ := hA.residueNormedCommRing; let _ := hA.residueNormedAlgebra
  have := hA.isUltrametricDist_residueNormedCommRing; have := hA.completeSpace_residueNormedCommRing
  exact coe_ofMap _

/-- Any Laurent domain `L(f, g⁻¹)` is an affinoid subdomain of `Sp A`, with no chosen norm on
`A`. -/
noncomputable def laurent (hA : IsAffinoidAlgebra K A) {r s : ℕ} (f : Fin r → A)
    (g : Fin s → A) : AffinoidSubdomain K A :=
  let _ := hA.residueNormedCommRing; let _ := hA.residueNormedAlgebra
  have := hA.isUltrametricDist_residueNormedCommRing; have := hA.completeSpace_residueNormedCommRing
  ofMap (LaurentFraction.isAffinoidSubdomainMap hA (f := f) (g := g))

@[simp]
theorem coe_laurent (hA : IsAffinoidAlgebra K A) {r s : ℕ} (f : Fin r → A) (g : Fin s → A) :
    (laurent hA f g : Set (MaximalSpectrum A)) = laurentDomain K f g := by
  let _ := hA.residueNormedCommRing; let _ := hA.residueNormedAlgebra
  have := hA.isUltrametricDist_residueNormedCommRing; have := hA.completeSpace_residueNormedCommRing
  exact coe_ofMap _

/-- The unit-sphere locus `{x ∈ Sp A : |f(x)| = 1}` as the Laurent subdomain `L(f, f⁻¹)`. -/
noncomputable def eqOne (hA : IsAffinoidAlgebra K A) (f : A) : AffinoidSubdomain K A :=
  laurent hA (fun _ : Fin 1 ↦ f) (fun _ : Fin 1 ↦ f)

@[simp]
theorem coe_eqOne (hA : IsAffinoidAlgebra K A) (f : A) :
    (eqOne hA f : Set (MaximalSpectrum A)) = {x | pointNorm K x f = 1} := by
  ext x; simp [eqOne, le_antisymm_iff]

/-- The closed rational sublevel subdomain `R(fⁿ / ϖ) = {x ∈ Sp A : |f(x)|ⁿ ≤ ‖ϖ‖}` for `ϖ ≠ 0`. -/
noncomputable def closedSublevelPow (hA : IsAffinoidAlgebra K A) (f : A) {ϖ : K} (hϖ : ϖ ≠ 0)
    (n : ℕ) : AffinoidSubdomain K A :=
  rational hA (Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span (Set.mem_insert _ _))
    ((Ne.isUnit hϖ).map (algebraMap K A)) :
    Ideal.span (insert (algebraMap K A ϖ) (Set.range (fun _ : Fin 1 ↦ f ^ n))) = ⊤)

@[simp]
theorem coe_closedSublevelPow (hA : IsAffinoidAlgebra K A) (f : A) {ϖ : K} (hϖ : ϖ ≠ 0) (n : ℕ) :
    (closedSublevelPow hA f hϖ n : Set (MaximalSpectrum A)) =
      {x | pointNorm K x f ^ n ≤ ‖ϖ‖} := by
  ext x; simp [closedSublevelPow, hϖ, x.pointNorm_pow]

end RationalLaurent

end TauCeti.AffinoidSubdomain
