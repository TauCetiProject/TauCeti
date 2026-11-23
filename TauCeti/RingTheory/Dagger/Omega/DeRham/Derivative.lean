/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Dagger.Omega.Forms
public import TauCeti.RingTheory.Derivation.ExteriorDerivative

/-!
# The overconvergent exterior derivative

For any commutative `R`-algebra `A` with Noetherian `Omega R A` (in particular any `K`-dagger
algebra over a complete ultrametric normed field `K`), `(Omega.d R A).TwistedExt` is Noetherian
over `A`, so `(Omega.d R A).derTwistedExt` lifts uniquely through `Omega.d R A`, yielding the
characteristic-free exterior derivative
`Omega.exteriorDeriv R A q : ⋀[A]^q (Omega R A) →ₗ[R] ⋀[A]^(q + 1) (Omega R A)`, its graded
Leibniz rule, `d ∘ d = 0`, and naturality along `formsMap`, without importing categorical homology
or the algebraic Kähler de Rham comparison.

## References

* E. Grosse-Klönne, *Finiteness of de Rham cohomology in rigid analysis*, Duke Math. J. 113
  (2002), §1.2.
* K. Kedlaya, *Finiteness of rigid cohomology with coefficients*, Duke Math. J. 134 (2006), §3.1.
-/

public section
noncomputable section

namespace TauCeti.Dagger.Omega

section ExteriorDeriv

variable (R A : Type*) [CommRing R] [CommRing A] [Algebra R A] [IsNoetherian A (Omega R A)]

/-- **The graded exterior derivative on `ExteriorAlgebra A (Omega R A)`.** -/
def exteriorAlgebraDeriv : ExteriorAlgebra A (Omega R A) →ₗ[R] ExteriorAlgebra A (Omega R A) :=
  (d R A).exteriorAlgebraDeriv (lift (d R A).derTwistedExt) (span_range_d R A)
    (lift_d (d R A).derTwistedExt)

/-- **The `q`-th exterior derivative `⋀[A]^q (Omega R A) →ₗ[R] ⋀[A]^(q + 1) (Omega R A)`.** -/
def exteriorDeriv (q : ℕ) : ⋀[A]^q (Omega R A) →ₗ[R] ⋀[A]^(q + 1) (Omega R A) :=
  (d R A).exteriorDeriv (lift (d R A).derTwistedExt) (span_range_d R A)
    (lift_d (d R A).derTwistedExt) q

section ExteriorDerivLemmas
variable {R A}

@[simp] theorem coe_exteriorDeriv_apply (q : ℕ) (ω : ⋀[A]^q (Omega R A)) :
    (exteriorDeriv R A q ω : ExteriorAlgebra A (Omega R A)) = exteriorAlgebraDeriv R A ω.val :=
  Derivation.coe_exteriorDeriv_apply _ _ _ _ q ω

@[simp] theorem exteriorAlgebraDeriv_algebraMap (a : A) :
    exteriorAlgebraDeriv R A (algebraMap A (ExteriorAlgebra A (Omega R A)) a) =
      ExteriorAlgebra.ι A (d R A a) := Derivation.exteriorAlgebraDeriv_algebraMap _ _ _ _ a

@[simp] theorem exteriorAlgebraDeriv_ι_apply (a : A) :
    exteriorAlgebraDeriv R A (ExteriorAlgebra.ι A (d R A a)) = 0 :=
  Derivation.exteriorAlgebraDeriv_ι_apply _ _ _ _ a

/-- **Ambient-algebra square-zero identity (`d ∘ d = 0`) on `ExteriorAlgebra A (Omega R A)`**,
for pointwise simplification of inhomogeneous elements. -/
@[simp] theorem exteriorAlgebraDeriv_exteriorAlgebraDeriv (x : ExteriorAlgebra A (Omega R A)) :
    exteriorAlgebraDeriv R A (exteriorAlgebraDeriv R A x) = 0 :=
  Derivation.exteriorAlgebraDeriv_exteriorAlgebraDeriv _ _ _ _ x

/-- **Graded Leibniz rule on `ExteriorAlgebra A (Omega R A)`.** -/
theorem exteriorAlgebraDeriv_mul (x y : ExteriorAlgebra A (Omega R A)) :
    exteriorAlgebraDeriv R A (x * y) =
      exteriorAlgebraDeriv R A x * y +
        CliffordAlgebra.involute (Q := (0 : QuadraticForm A (Omega R A))) x *
          exteriorAlgebraDeriv R A y :=
  Derivation.exteriorAlgebraDeriv_mul _ _ _ _ x y

/-- Graded Leibniz rule on `ExteriorAlgebra A (Omega R A)` for a left factor in
`⋀[A]^p (Omega R A)`, with sign `(-1) ^ p` determined by the left factor's degree. -/
theorem exteriorAlgebraDeriv_mul_of_mem_exteriorPower {p : ℕ} {x : ExteriorAlgebra A (Omega R A)}
    (hx : x ∈ ⋀[A]^p (Omega R A)) (y : ExteriorAlgebra A (Omega R A)) :
    exteriorAlgebraDeriv R A (x * y) =
      exteriorAlgebraDeriv R A x * y + (-1 : A) ^ p • (x * exteriorAlgebraDeriv R A y) :=
  Derivation.exteriorAlgebraDeriv_mul_of_mem_exteriorPower _ _ _ _ hx y

/-- **Degree-zero identification (`simp` direction)**: under `zeroEquiv` and `oneEquiv`,
`Omega.exteriorDeriv R A 0` identifies with `Omega.d R A`, rewriting
`(zeroEquiv A (Omega R A)).symm a` to `(oneEquiv A (Omega R A)).symm (d R A a)`. See
`oneEquiv_exteriorDeriv_zero` for the forward-equivalence direction extracting `Omega.d R A`. -/
@[simp] theorem exteriorDeriv_zero_symm (a : A) :
    exteriorDeriv R A 0 ((exteriorPower.zeroEquiv A (Omega R A)).symm a) =
      (exteriorPower.oneEquiv A (Omega R A)).symm (d R A a) :=
  Derivation.exteriorDeriv_zero_symm _ _ _ _ a

/-- **Degree-zero identification (forward-equivalence direction)**: under `zeroEquiv` and
`oneEquiv`, `Omega.exteriorDeriv R A 0` recovers `Omega.d R A` as
`oneEquiv A (Omega R A) (d ω) = d R A (zeroEquiv A (Omega R A) ω)`. See `exteriorDeriv_zero_symm`
for the `simp` direction. -/
theorem oneEquiv_exteriorDeriv_zero (ω : ⋀[A]^0 (Omega R A)) :
    exteriorPower.oneEquiv A (Omega R A) (exteriorDeriv R A 0 ω) =
      d R A (exteriorPower.zeroEquiv A (Omega R A) ω) :=
  Derivation.oneEquiv_exteriorDeriv_zero _ _ _ _ ω

/-- **Pointwise homogeneous square-zero identity** `d (d ω) = 0` for an overconvergent `q`-form
`ω`, used for `simp` rewriting. -/
@[simp] theorem exteriorDeriv_exteriorDeriv_apply (q : ℕ) (ω : ⋀[A]^q (Omega R A)) :
    exteriorDeriv R A (q + 1) (exteriorDeriv R A q ω) = 0 :=
  Derivation.exteriorDeriv_exteriorDeriv_apply _ _ _ _ q ω

/-- **Bundled square-zero composition** `d_{q+1} ∘ₗ d_q = 0` as `R`-linear maps on exterior
powers of `Omega R A`, used to construct `deRhamComplex R A`. -/
theorem exteriorDeriv_comp_exteriorDeriv (q : ℕ) :
    (exteriorDeriv R A (q + 1)) ∘ₗ (exteriorDeriv R A q) = 0 :=
  Derivation.exteriorDeriv_comp_exteriorDeriv _ _ _ _ q

/-- **Scalar Leibniz rule on overconvergent `q`-forms**: `d (a • ω) = d a ∧ ω + a • d ω`. -/
theorem exteriorDeriv_smul (q : ℕ) (a : A) (ω : ⋀[A]^q (Omega R A)) :
    exteriorDeriv R A q (a • ω) =
      TauCeti.ExteriorAlgebra.wedgeLeft (d R A a) q ω + a • exteriorDeriv R A q ω :=
  Derivation.exteriorDeriv_smul _ _ _ _ q a ω

/-- Every wedge product `d b₀ ∧ ⋯ ∧ d b_{q-1}` of exact differentials is closed (`d = 0`). -/
@[simp] theorem exteriorDeriv_ιMulti_comp_d {q : ℕ} (b : Fin q → A) :
    exteriorDeriv R A q (exteriorPower.ιMulti A q (d R A ∘ b)) = 0 :=
  Derivation.exteriorDeriv_ιMulti_comp_D _ _ _ _ b

/-- **Formula on scaled exact-differential wedges**: since `d b₀ ∧ ⋯ ∧ d b_{q-1}` is closed,
only its scalar coefficient `a` is differentiated:
`d (a • (d b₀ ∧ ⋯ ∧ d b_{q-1})) = d a ∧ d b₀ ∧ ⋯ ∧ d b_{q-1}`. -/
theorem exteriorDeriv_smul_ιMulti_comp_d {q : ℕ} (a : A) (b : Fin q → A) :
    exteriorDeriv R A q (a • exteriorPower.ιMulti A q (d R A ∘ b)) =
      exteriorPower.ιMulti A (q + 1) (Fin.cons (d R A a) (d R A ∘ b)) :=
  Derivation.exteriorDeriv_smul_ιMulti_comp_D _ _ _ _ a b

/-- **Graded Leibniz rule for `exteriorPower.wedge`** of a `p`-form and a `q`-form, with sign
`(-1) ^ p` determined by the left factor's degree. -/
theorem exteriorDeriv_wedge (p q : ℕ) (ω : ⋀[A]^p (Omega R A)) (η : ⋀[A]^q (Omega R A)) :
    exteriorDeriv R A (p + q) (exteriorPower.wedge A (Omega R A) p q ω η) =
      LinearEquiv.ofEq _ _ (congrArg (⋀[A]^· (Omega R A)) (Nat.add_right_comm p 1 q))
        (exteriorPower.wedge A (Omega R A) (p + 1) q (exteriorDeriv R A p ω) η) +
        (-1 : A) ^ p • exteriorPower.wedge A (Omega R A) p (q + 1) ω (exteriorDeriv R A q η) :=
  Derivation.exteriorDeriv_wedge _ _ _ _ p q ω η

end ExteriorDerivLemmas
end ExteriorDeriv

section Functoriality
variable {K A B : Type*} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  [CommRing A] [CommRing B] [Algebra K A] [Algebra K B]
  [IsDaggerAlgebra K A] [IsDaggerAlgebra K B]

/-- **Naturality of `exteriorDeriv` along a homomorphism of dagger algebras.** -/
theorem mapSemilinear_exteriorDeriv (f : A →ₐ[K] B) (q : ℕ) (ω : ⋀[A]^q (Omega K A)) :
    exteriorPower.mapSemilinear (q + 1) (mapSemilinear f) (exteriorDeriv K A q ω) =
      exteriorDeriv K B q (exteriorPower.mapSemilinear q (mapSemilinear f) ω) :=
  Derivation.mapSemilinear_exteriorDeriv _ _ _ _ _ _ _ _ f (mapSemilinear f) (mapSemilinear_d f) q ω

theorem exteriorDeriv_formsMap (f : A →ₐ[K] B) (q : ℕ) (ω : ⋀[A]^q (Omega K A)) :
    exteriorDeriv K B q (formsMap f q ω) = formsMap f (q + 1) (exteriorDeriv K A q ω) := by
  simpa only [formsMap_apply] using (mapSemilinear_exteriorDeriv f q ω).symm

theorem exteriorDeriv_comp_formsMap (f : A →ₐ[K] B) (q : ℕ) :
    (exteriorDeriv K B q) ∘ₗ (formsMap f q) = (formsMap f (q + 1)) ∘ₗ (exteriorDeriv K A q) :=
  LinearMap.ext (exteriorDeriv_formsMap f q)

end Functoriality

end TauCeti.Dagger.Omega
