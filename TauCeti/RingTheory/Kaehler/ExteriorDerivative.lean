/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Derivation.ExteriorDerivative
public import TauCeti.RingTheory.Kaehler.MapSemilinear

/-!
# Algebraic exterior derivative on Kähler differentials

Specialises `Derivation.exteriorAlgebraDeriv` and `Derivation.exteriorDeriv` to
`KaehlerDifferential.D R A`, defining `KaehlerDifferential.exteriorDeriv R A q` and its properties.
-/

public section

namespace KaehlerDifferential
variable (R A : Type*) [CommRing R] [CommRing A] [Algebra R A]

/-- **The algebraic exterior derivative on `ExteriorAlgebra A Ω[A⁄R]`.** -/
noncomputable def exteriorAlgebraDeriv : ExteriorAlgebra A Ω[A⁄R] →ₗ[R] ExteriorAlgebra A Ω[A⁄R] :=
  (D R A).exteriorAlgebraDeriv (D R A).derTwistedExt.liftKaehlerDifferential
    (span_range_derivation R A) (D R A).derTwistedExt.liftKaehlerDifferential_comp_D

/-- **The `q`-th algebraic exterior derivative** `⋀[A]^q Ω[A⁄R] →ₗ[R] ⋀[A]^(q + 1) Ω[A⁄R]`. -/
noncomputable def exteriorDeriv (q : ℕ) : ⋀[A]^q Ω[A⁄R] →ₗ[R] ⋀[A]^(q + 1) Ω[A⁄R] :=
  (D R A).exteriorDeriv (D R A).derTwistedExt.liftKaehlerDifferential
    (span_range_derivation R A) (D R A).derTwistedExt.liftKaehlerDifferential_comp_D q

variable {R A}
@[simp] theorem coe_exteriorDeriv_apply (q : ℕ) (ω : ⋀[A]^q Ω[A⁄R]) :
    (exteriorDeriv R A q ω : ExteriorAlgebra A Ω[A⁄R]) = exteriorAlgebraDeriv R A ω.val :=
  Derivation.coe_exteriorDeriv_apply _ _ _ _ q ω
@[simp] theorem exteriorDeriv_zero_symm (a : A) :
    exteriorDeriv R A 0 ((exteriorPower.zeroEquiv A Ω[A⁄R]).symm a) =
      (exteriorPower.oneEquiv A Ω[A⁄R]).symm (D R A a) :=
  Derivation.exteriorDeriv_zero_symm _ _ _ _ a
/-- **Pointwise homogeneous square-zero identity** `d (d ω) = 0` on Kähler `q`-forms, used for
`simp` rewriting. -/
@[simp] theorem exteriorDeriv_exteriorDeriv_apply (q : ℕ) (ω : ⋀[A]^q Ω[A⁄R]) :
    exteriorDeriv R A (q + 1) (exteriorDeriv R A q ω) = 0 :=
  Derivation.exteriorDeriv_exteriorDeriv_apply _ _ _ _ q ω
/-- **Scalar Leibniz rule on Kähler `q`-forms**: `d (a • ω) = D a ∧ ω + a • d ω`. -/
theorem exteriorDeriv_smul (q : ℕ) (a : A) (ω : ⋀[A]^q Ω[A⁄R]) :
    exteriorDeriv R A q (a • ω) =
      TauCeti.ExteriorAlgebra.wedgeLeft (D R A a) q ω + a • exteriorDeriv R A q ω :=
  Derivation.exteriorDeriv_smul _ _ _ _ q a ω
/-- Every wedge product `D b₀ ∧ ⋯ ∧ D b_{q-1}` of exact Kähler differentials is closed (`d = 0`). -/
@[simp] theorem exteriorDeriv_ιMulti_comp_D {q : ℕ} (b : Fin q → A) :
    exteriorDeriv R A q (exteriorPower.ιMulti A q (D R A ∘ b)) = 0 :=
  Derivation.exteriorDeriv_ιMulti_comp_D _ _ _ _ b
/-- **Formula on scaled exact-differential wedges**: since `D b₀ ∧ ⋯ ∧ D b_{q-1}` is closed,
only its scalar coefficient `a` is differentiated:
`d (a • (D b₀ ∧ ⋯ ∧ D b_{q-1})) = D a ∧ D b₀ ∧ ⋯ ∧ D b_{q-1}`. -/
theorem exteriorDeriv_smul_ιMulti_comp_D {q : ℕ} (a : A) (b : Fin q → A) :
    exteriorDeriv R A q (a • exteriorPower.ιMulti A q (D R A ∘ b)) =
      exteriorPower.ιMulti A (q + 1) (Fin.cons (D R A a) (D R A ∘ b)) :=
  Derivation.exteriorDeriv_smul_ιMulti_comp_D _ _ _ _ a b
/-- Universal naturality of `KaehlerDifferential.exteriorDeriv` along a semilinear map
sending `D R A a` to `D' (f a)`. -/
theorem mapSemilinear_exteriorDeriv_of_derivation {B N : Type*} [CommRing B] [Algebra R B]
    [AddCommGroup N] [Module R N] [Module B N] [IsScalarTower R B N]
    (D' : Derivation R B N) (u' : N →ₗ[B] Derivation.TwistedExt D')
    (hspan' : Submodule.span B (Set.range D') = ⊤) (hu' : ∀ b, u' (D' b) = D'.derTwistedExt b)
    (f : A →ₐ[R] B) (g : Ω[A⁄R] →ₛₗ[f.toRingHom] N)
    (hg : ∀ a, g (D R A a) = D' (f a)) (q : ℕ) (ω : ⋀[A]^q Ω[A⁄R]) :
    exteriorPower.mapSemilinear (q + 1) g (exteriorDeriv R A q ω) =
      D'.exteriorDeriv u' hspan' hu' q (exteriorPower.mapSemilinear q g ω) :=
  Derivation.mapSemilinear_exteriorDeriv _ _ _ _ D' u' hspan' hu' f g hg q ω
/-- An `R`-algebra homomorphism `f : A →ₐ[R] B` induces maps on Kähler `q`-forms via
`KaehlerDifferential.mapSemilinear f` that commute with the algebraic exterior derivative. -/
theorem mapSemilinear_exteriorDeriv {B : Type*} [CommRing B] [Algebra R B]
    (f : A →ₐ[R] B) (q : ℕ) (ω : ⋀[A]^q Ω[A⁄R]) :
    exteriorPower.mapSemilinear (q + 1) (KaehlerDifferential.mapSemilinear f)
        (exteriorDeriv R A q ω) =
      exteriorDeriv R B q (exteriorPower.mapSemilinear q (KaehlerDifferential.mapSemilinear f) ω) :=
  mapSemilinear_exteriorDeriv_of_derivation _ _ _ _ f (KaehlerDifferential.mapSemilinear f)
    (KaehlerDifferential.mapSemilinear_D f) q ω
end KaehlerDifferential
