/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.HomologicalComplex.Projective.Dimension
public import TauCeti.Algebra.Homology.UniversalCoefficient.Naturality
public import TauCeti.AlgebraicTopology.Cohomology.Twisted.Kronecker

/-!
# The universal coefficient theorem for singular cohomology with local coefficients

Let `L` be a local coefficient system of `R`-modules on a space `X` whose fibres are projective,
for instance the integral orientation system of a manifold or of a vector bundle, and let `M` be an
`R`-module. The twisted singular chain modules `Cₙ(X; L)` are direct sums of fibres of `L`, hence
projective (`TauCeti.LocalCoefficientSystem.projective_twistedChainComplex_X`), and so are the
relative ones of a pair (`TopPair.projective_twistedChainComplex_X`). These are the hypotheses of
the algebraic universal coefficient theorem (`TauCeti.Algebra.Homology.UniversalCoefficient.Basic`)
for the twisted cochains `Hom(C(X; L), M)`, with the twisted Kronecker map
`TauCeti.LocalCoefficientSystem.twistedKronecker` evaluating cohomology on homology:

* **projective homology below `n`**, over any ring `R`: if `Hⱼ(X; L)` is projective for `j < n`,
  for instance zero, the Kronecker map `Hⁿ(X; L, M) →ₗ[k] (Hₙ(X; L) ⟶ M)` is bijective
  (`TauCeti.LocalCoefficientSystem.twistedKronecker_bijective_of_projective_homology_lt`);
* **over a hereditary ring**, such as `ℤ` or another principal ideal domain, the sequence
  `0 ⟶ Ext¹(Hₙ(X; L), M) ⟶ Hⁿ⁺¹(X; L, M) ⟶ Hom(Hₙ₊₁(X; L), M) ⟶ 0`
  is exact (`TauCeti.LocalCoefficientSystem.twistedExtToCohomology_injective`,
  `TauCeti.LocalCoefficientSystem.exact_twistedExtToCohomology_twistedKronecker`,
  `TauCeti.LocalCoefficientSystem.twistedKronecker_surjective`), its first map is natural in the
  space and in the local system, and it splits, non-naturally
  (`TauCeti.LocalCoefficientSystem.twistedUniversalCoefficientEquiv`). A single projective
  homology module `Hₙ(X; L)` already makes the Kronecker map bijective in degree `n + 1`
  (`TauCeti.LocalCoefficientSystem.twistedKronecker_bijective_succ_of_projective_homology`).

The same statements, except the naturality of the first map, hold for the relative twisted
cohomology of a pair `(X, A)`, in the namespace `TopPair`. With the vanishing of relative homology
below a degree this gives the bottom degree of relative cohomology: if `Hⱼ(X, A; L) = 0` for
`j < n`, then `Hⁿ(X, A; L, M)` is `Hom(Hₙ(X, A; L), M)`
(`TopPair.twistedKronecker_bijective_of_projective_homology_lt`). For the Thom pair `(E, E₀)` of a
real vector bundle of rank `r`, whose relative homology with any local coefficients vanishes below
`r`, this identifies `Hʳ(E, E₀; L, M)` with `Hom(Hᵣ(E, E₀; L), M)`
(`TauCeti.thomPairTwistedCohomologyFinrankEquiv`); with `L` the orientation system pulled back to
`E`, this is the degree of a Thom class with orientation-twisted coefficients.

This is the twisted counterpart of `TauCeti.AlgebraicTopology.Cohomology.UniversalCoefficient`, to
which it reduces for a constant system with fibre `R`
(`TauCeti.LocalCoefficientSystem.twistedCohomologyConstantIso`).

## Main declarations

* `TauCeti.LocalCoefficientSystem.twistedKronecker_bijective_of_projective_homology_lt`,
  `TauCeti.LocalCoefficientSystem.twistedKronecker_bijective_of_projective_homology` and
  `TauCeti.LocalCoefficientSystem.twistedKroneckerEquivOfProjectiveHomology`: the Kronecker map is
  bijective in degree `n` when twisted homology is projective below `n`, and in every degree when
  it is projective in every degree.
* `TauCeti.LocalCoefficientSystem.twistedKronecker_bijective_succ_of_projective_homology`,
  `TauCeti.LocalCoefficientSystem.twistedKroneckerEquivSuccOfProjectiveHomology` and
  `TauCeti.LocalCoefficientSystem.isZero_twistedCohomology_succ_of_projective_homology`: over a
  hereditary ring, the Kronecker map is bijective in degree `n + 1` when `Hₙ(X; L)` is projective,
  and cohomology vanishes there when moreover `Hₙ₊₁(X; L) = 0`.
* `TauCeti.LocalCoefficientSystem.twistedExtToCohomology`: the map
  `Ext¹(Hₙ(X; L), M) →ₗ[k] Hⁿ⁺¹(X; L, M)`, characterized by
  `TauCeti.LocalCoefficientSystem.twistedExtToCohomology_extClass_comp_mk₀`, with its exactness
  statements, its naturality, the section
  `TauCeti.LocalCoefficientSystem.twistedKroneckerSection` and the splitting
  `TauCeti.LocalCoefficientSystem.twistedUniversalCoefficientEquiv`.
* The relative forms in the namespace `TopPair`, with the same names; the naturality lemmas
  `TauCeti.LocalCoefficientSystem.twistedExtToCohomology_twistedHomologyCoefficientMap` and
  `TauCeti.LocalCoefficientSystem.twistedExtToCohomology_twistedHomologyMap` are stated only in the
  absolute case.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 3.1, Theorem 3.2, and Section 3.H.
* C. Weibel, *An Introduction to Homological Algebra*, Section 3.6.
-/

public section

noncomputable section

open CategoryTheory Limits Abelian

universe t u v w

namespace TauCeti.LocalCoefficientSystem

section ProjectiveHomology

variable {R : Type u} [Ring R] (k : Type*) [Ring k] [Linear k (ModuleCat.{max v w} R)]
  (M : ModuleCat.{max v w} R) {X : TopCat.{v}} (L : LocalCoefficientSystem.{u, v, max v w} R X)
  [∀ x, Projective (L.obj x)]

/-- **The universal coefficient theorem with local coefficients below the first non-projective
homology**, over any ring `R`: for a local system `L` with projective fibres, if the twisted
homology modules `Hⱼ(X; L)` are projective for `j < n`, for instance zero, the Kronecker map
`Hⁿ(X; L, M) →ₗ[k] (Hₙ(X; L) ⟶ M)` is bijective, for every module `M`. -/
theorem twistedKronecker_bijective_of_projective_homology_lt (n : ℕ)
    (h : ∀ j < n, Projective (L.twistedHomology j)) :
    Function.Bijective (L.twistedKronecker k (M := M) n) :=
  by
  rw [twistedKronecker_def]
  exact TauCeti.ChainComplex.kronecker_bijective_of_projective_homology_lt n h

/-- **The universal coefficient theorem with local coefficients and projective homology**: for a
local system `L` with projective fibres whose twisted homology modules `Hₙ(X; L)` are all
projective, the Kronecker map `Hⁿ(X; L, M) →ₗ[k] (Hₙ(X; L) ⟶ M)` is bijective in every degree, for
every module `M`. -/
theorem twistedKronecker_bijective_of_projective_homology
    [∀ n, Projective (L.twistedHomology n)] (n : ℕ) :
    Function.Bijective (L.twistedKronecker k (M := M) n) :=
  L.twistedKronecker_bijective_of_projective_homology_lt k M n fun _ _ ↦ inferInstance

/-- **The universal coefficient isomorphism with local coefficients and projective homology**: for
a local system `L` with projective fibres whose twisted homology modules are all projective, the
Kronecker map is a `k`-linear equivalence `Hⁿ(X; L, M) ≃ₗ[k] (Hₙ(X; L) ⟶ M)`. -/
def twistedKroneckerEquivOfProjectiveHomology [∀ n, Projective (L.twistedHomology n)] (n : ℕ) :
    L.twistedCohomology k M n ≃ₗ[k] (L.twistedHomology n ⟶ M) :=
  LinearEquiv.ofBijective _ (L.twistedKronecker_bijective_of_projective_homology k M n)

/-- The equivalence `TauCeti.LocalCoefficientSystem.twistedKroneckerEquivOfProjectiveHomology` is
the Kronecker map. -/
@[simp]
lemma twistedKroneckerEquivOfProjectiveHomology_apply [∀ n, Projective (L.twistedHomology n)]
    (n : ℕ) (α : L.twistedCohomology k M n) :
    L.twistedKroneckerEquivOfProjectiveHomology k M n α = L.twistedKronecker k n α :=
  (rfl)

end ProjectiveHomology

section HereditarySingleDegree

variable {R : Type u} [Ring R] [∀ V : ModuleCat.{max v w} R, HasProjectiveDimensionLE V 1]
  (k : Type*) [Ring k] [Linear k (ModuleCat.{max v w} R)] (M : ModuleCat.{max v w} R)
  {X : TopCat.{v}} (L : LocalCoefficientSystem.{u, v, max v w} R X) [∀ x, Projective (L.obj x)]

/-- **The universal coefficient theorem with local coefficients above a projective homology
module**, when every `R`-module has projective dimension at most one, as over `ℤ`: for a local
system `L` with projective fibres, if `Hₙ(X; L)` is projective, the Kronecker map
`Hⁿ⁺¹(X; L, M) →ₗ[k] (Hₙ₊₁(X; L) ⟶ M)` is bijective, for every module `M`. Nothing is assumed about
the homology in the other degrees. -/
theorem twistedKronecker_bijective_succ_of_projective_homology (n : ℕ)
    [Projective (L.twistedHomology n)] :
    Function.Bijective (L.twistedKronecker k (M := M) (n + 1)) :=
  by
  rw [twistedKronecker_def]
  exact TauCeti.ChainComplex.kronecker_bijective_succ_of_projective_homology n

/-- **The universal coefficient isomorphism with local coefficients above a projective homology
module**, when every `R`-module has projective dimension at most one: if `Hₙ(X; L)` is projective,
the Kronecker map is a `k`-linear equivalence `Hⁿ⁺¹(X; L, M) ≃ₗ[k] (Hₙ₊₁(X; L) ⟶ M)`. -/
def twistedKroneckerEquivSuccOfProjectiveHomology (n : ℕ) [Projective (L.twistedHomology n)] :
    L.twistedCohomology k M (n + 1) ≃ₗ[k] (L.twistedHomology (n + 1) ⟶ M) :=
  LinearEquiv.ofBijective _ (L.twistedKronecker_bijective_succ_of_projective_homology k M n)

/-- The equivalence `TauCeti.LocalCoefficientSystem.twistedKroneckerEquivSuccOfProjectiveHomology`
is the Kronecker map. -/
@[simp]
lemma twistedKroneckerEquivSuccOfProjectiveHomology_apply (n : ℕ)
    [Projective (L.twistedHomology n)] (α : L.twistedCohomology k M (n + 1)) :
    L.twistedKroneckerEquivSuccOfProjectiveHomology k M n α = L.twistedKronecker k (n + 1) α :=
  (rfl)

/-- **Twisted cohomology vanishes above a projective homology module followed by a zero one**,
when every `R`-module has projective dimension at most one: for a local system `L` with projective
fibres, if `Hₙ(X; L)` is projective and `Hₙ₊₁(X; L) = 0`, then `Hⁿ⁺¹(X; L, M) = 0` for every module
`M`. -/
theorem isZero_twistedCohomology_succ_of_projective_homology (n : ℕ)
    [Projective (L.twistedHomology n)] (h : IsZero (L.twistedHomology (n + 1))) :
    IsZero (L.twistedCohomology k M (n + 1)) :=
  TauCeti.ChainComplex.isZero_homology_linearYonedaObj_succ_of_projective_homology n h

/-- **The splitting of the universal coefficient sequence with local coefficients**: a `k`-linear
right inverse `Hom(Hₙ(X; L), M) →ₗ[k] Hⁿ(X; L, M)` of the Kronecker map. It sends `g` to the class
of the cocycle `Cₙ(X; L) ⟶ Zₙ ⟶ Hₙ(X; L) ⟶ M`, through a chosen retraction of the inclusion of the
twisted cycles, and need not be natural in `X`. -/
def twistedKroneckerSection (n : ℕ) :
    (L.twistedHomology n ⟶ M) →ₗ[k] L.twistedCohomology k M n :=
  TauCeti.ChainComplex.kroneckerSection k L.twistedChainComplex M n

/-- `TauCeti.LocalCoefficientSystem.twistedKroneckerSection` is a right inverse of the Kronecker
map. -/
@[simp]
lemma twistedKronecker_twistedKroneckerSection (n : ℕ) (g : L.twistedHomology n ⟶ M) :
    L.twistedKronecker k n (L.twistedKroneckerSection k M n g) = g :=
  by
  rw [twistedKronecker_def]
  exact TauCeti.ChainComplex.kronecker_kroneckerSection n g

/-- **Surjectivity in the universal coefficient sequence with local coefficients**: when every
`R`-module has projective dimension at most one, every morphism `Hₙ(X; L) ⟶ M` is the evaluation of
a class in `Hⁿ(X; L, M)`. -/
theorem twistedKronecker_surjective (n : ℕ) :
    Function.Surjective (L.twistedKronecker k (M := M) n) :=
  by
  rw [twistedKronecker_def]
  exact TauCeti.ChainComplex.kronecker_surjective_of_isSplitMono n

end HereditarySingleDegree

section Hereditary

variable {R : Type u} [Ring R] [∀ V : ModuleCat.{max v w} R, HasProjectiveDimensionLE V 1]
  [HasExt.{t} (ModuleCat.{max v w} R)] (k : Type*) [CommRing k]
  [Linear k (ModuleCat.{max v w} R)] (M : ModuleCat.{max v w} R) {X : TopCat.{v}}
  (L : LocalCoefficientSystem.{u, v, max v w} R X) [∀ x, Projective (L.obj x)]

/-- **The `Ext` term of the universal coefficient sequence with local coefficients**, when every
`R`-module has projective dimension at most one: the `k`-linear map
`Ext¹(Hₙ(X; L), M) →ₗ[k] Hⁿ⁺¹(X; L, M)`. It is the algebraic map
`TauCeti.ChainComplex.extToHomology` of the twisted chain complex: an extension class represented
by a morphism `β : Bₙ ⟶ M` out of the twisted boundaries goes to the class of the cocycle
`Cₙ₊₁(X; L) ⟶ Bₙ ⟶ M`. -/
def twistedExtToCohomology (n : ℕ) :
    Ext.{t} (L.twistedHomology n) M 1 →ₗ[k] L.twistedCohomology k M (n + 1) :=
  TauCeti.ChainComplex.extToHomology k L.twistedChainComplex M (n + 1) n

/-- The `Ext` term of the universal coefficient sequence with local coefficients is the algebraic
map `TauCeti.ChainComplex.extToHomology` of the twisted chain complex. -/
lemma twistedExtToCohomology_def (n : ℕ) :
    L.twistedExtToCohomology k M n =
      TauCeti.ChainComplex.extToHomology k L.twistedChainComplex M (n + 1) n :=
  (rfl)

/-- **The characterization of `TauCeti.LocalCoefficientSystem.twistedExtToCohomology`**: the class
in `Ext¹(Hₙ(X; L), M)` of a morphism `β : Bₙ ⟶ M` out of the twisted boundaries
`Bₙ = ker(Zₙ ⟶ Hₙ(X; L))` goes to the class of the cocycle `Cₙ₊₁(X; L) ⟶ Bₙ ⟶ M`. -/
lemma twistedExtToCohomology_extClass_comp_mk₀ (n : ℕ)
    (β : kernel (L.twistedChainComplex.homologyπ n) ⟶ M)
    (φ : (L.twistedCochainComplex k M).cycles (n + 1))
    (hφ : (L.twistedCochainComplex k M).iCycles (n + 1) φ =
      L.twistedChainComplex.toBoundaries (n + 1) n ≫ β) :
    L.twistedExtToCohomology k M n
        ((TauCeti.kernelSequence_shortExact
          (L.twistedChainComplex.homologyπ n)).extClass.comp (Ext.mk₀ β) (add_zero 1)) =
      (L.twistedCochainComplex k M).homologyπ (n + 1) φ :=
  TauCeti.ChainComplex.extToHomology_extClass_comp_mk₀ (n + 1) n β φ hφ

/-- **Injectivity in the universal coefficient sequence with local coefficients**: when every
`R`-module has projective dimension at most one, the map `Ext¹(Hₙ(X; L), M) →ₗ[k] Hⁿ⁺¹(X; L, M)`
is injective. -/
theorem twistedExtToCohomology_injective (n : ℕ) :
    Function.Injective (L.twistedExtToCohomology k M n) :=
  TauCeti.ChainComplex.extToHomology_injective rfl

/-- **Exactness in the middle of the universal coefficient sequence with local coefficients**:
when every `R`-module has projective dimension at most one, a class in `Hⁿ⁺¹(X; L, M)` evaluates to
zero on `Hₙ₊₁(X; L)` exactly when it comes from `Ext¹(Hₙ(X; L), M)`. -/
theorem exact_twistedExtToCohomology_twistedKronecker (n : ℕ) :
    Function.Exact (L.twistedExtToCohomology k M n) (L.twistedKronecker k (M := M) (n + 1)) :=
  by
  rw [twistedKronecker_def]
  exact TauCeti.ChainComplex.exact_extToHomology_kronecker rfl

/-- **The splitting of the universal coefficient sequence with local coefficients**, when every
`R`-module has projective dimension at most one: a `k`-linear equivalence
`Hⁿ⁺¹(X; L, M) ≃ₗ[k] Ext¹(Hₙ(X; L), M) × Hom(Hₙ₊₁(X; L), M)` whose second component is the
Kronecker map (`TauCeti.LocalCoefficientSystem.twistedUniversalCoefficientEquiv_apply_snd`) and
whose inverse restricts to `TauCeti.LocalCoefficientSystem.twistedExtToCohomology` on the first
factor (`TauCeti.LocalCoefficientSystem.twistedUniversalCoefficientEquiv_symm_inl`). It is built
from the section `TauCeti.LocalCoefficientSystem.twistedKroneckerSection` and is not natural in
`X`. -/
def twistedUniversalCoefficientEquiv (n : ℕ) :
    L.twistedCohomology k M (n + 1) ≃ₗ[k]
      Ext.{t} (L.twistedHomology n) M 1 × (L.twistedHomology (n + 1) ⟶ M) :=
  TauCeti.ChainComplex.universalCoefficientEquiv k L.twistedChainComplex M rfl

/-- The inverse of the splitting `TauCeti.LocalCoefficientSystem.twistedUniversalCoefficientEquiv`
restricts to the inclusion `TauCeti.LocalCoefficientSystem.twistedExtToCohomology` of the `Ext`
term on the first factor. -/
@[simp]
lemma twistedUniversalCoefficientEquiv_symm_inl (n : ℕ)
    (e : Ext.{t} (L.twistedHomology n) M 1) :
    (L.twistedUniversalCoefficientEquiv k M n).symm (e, 0) = L.twistedExtToCohomology k M n e :=
  TauCeti.ChainComplex.universalCoefficientEquiv_symm_inl rfl e

/-- The second component of the splitting
`TauCeti.LocalCoefficientSystem.twistedUniversalCoefficientEquiv` is the Kronecker map. -/
@[simp]
lemma twistedUniversalCoefficientEquiv_apply_snd (n : ℕ)
    (x : L.twistedCohomology k M (n + 1)) :
    (L.twistedUniversalCoefficientEquiv k M n x).2 = L.twistedKronecker k (n + 1) x :=
  by
  rw [twistedKronecker_def]
  exact TauCeti.ChainComplex.universalCoefficientEquiv_apply_snd rfl x

end Hereditary

section HereditaryNaturality

variable {R : Type u} [Ring R] [∀ V : ModuleCat.{max v w} R, HasProjectiveDimensionLE V 1]
  [HasExt.{t} (ModuleCat.{max v w} R)] (k : Type*) [CommRing k]
  [Linear k (ModuleCat.{max v w} R)] (M : ModuleCat.{max v w} R) {X : TopCat.{v}}

/-- **Naturality of the universal coefficient sequence with local coefficients in the local
system**: for a morphism `η : L ⟶ K` of local systems with projective fibres, pulling an extension
back along `η_* : Hₙ(X; L) ⟶ Hₙ(X; K)` and then including it in `Hⁿ⁺¹(X; L, M)` is including it in
`Hⁿ⁺¹(X; K, M)` and then pulling back along `η`. -/
lemma twistedExtToCohomology_twistedHomologyCoefficientMap
    {L K : LocalCoefficientSystem.{u, v, max v w} R X} [∀ x, Projective (L.obj x)]
    [∀ x, Projective (K.obj x)] (η : L ⟶ K) (n : ℕ) (e : Ext.{t} (K.twistedHomology n) M 1) :
    L.twistedExtToCohomology k M n
        ((Ext.mk₀ (twistedHomologyCoefficientMap η n)).comp e (zero_add 1)) =
      twistedCohomologyCoefficientMap k M η (n + 1) (K.twistedExtToCohomology k M n e) :=
  TauCeti.ChainComplex.extToHomology_naturality (twistedChainComplexCoefficientMap η) (n + 1) n e

/-- **Naturality of the universal coefficient sequence with local coefficients in the space**: for
a continuous map `f : X ⟶ Y` and a local system `L` on `Y` with projective fibres, pulling an
extension back along `f_* : Hₙ(X; f^*L) ⟶ Hₙ(Y; L)` and then including it in
`Hⁿ⁺¹(X; f^*L, M)` is including it in `Hⁿ⁺¹(Y; L, M)` and then pulling back along `f`. -/
lemma twistedExtToCohomology_twistedHomologyMap {Y : TopCat.{v}} (f : X ⟶ Y)
    (L : LocalCoefficientSystem.{u, v, max v w} R Y) [∀ y, Projective (L.obj y)] (n : ℕ)
    (e : Ext.{t} (L.twistedHomology n) M 1) :
    ((pullback f.hom).obj L).twistedExtToCohomology k M n
        ((Ext.mk₀ (twistedHomologyMap f L n)).comp e (zero_add 1)) =
      twistedCohomologyMap k M f L (n + 1) (L.twistedExtToCohomology k M n e) :=
  TauCeti.ChainComplex.extToHomology_naturality (twistedChainComplexMap f L) (n + 1) n e

end HereditaryNaturality

end TauCeti.LocalCoefficientSystem

namespace TopPair

open TauCeti

section ProjectiveHomology

variable {R : Type u} [Ring R] (P : TopPair.{v})
  (L : LocalCoefficientSystem.{u, v, max v w} R P.fst) (k : Type*) [Ring k]
  [Linear k (ModuleCat.{max v w} R)] (M : ModuleCat.{max v w} R)
  [∀ x, Projective (L.obj x)]

/-- **The relative universal coefficient theorem with local coefficients below the first
non-projective homology**, over any ring `R`: for a local system `L` with projective fibres on the
ambient space of a pair, if the relative twisted homology modules `Hⱼ(X, A; L)` are projective for
`j < n`, for instance zero, the relative Kronecker map
`Hⁿ(X, A; L, M) →ₗ[k] (Hₙ(X, A; L) ⟶ M)` is bijective, for every module `M`. -/
theorem twistedKronecker_bijective_of_projective_homology_lt (n : ℕ)
    (h : ∀ j < n, Projective (P.twistedHomology L j)) :
    Function.Bijective (P.twistedKronecker L k (M := M) n) :=
  by
  rw [twistedKronecker_def]
  exact TauCeti.ChainComplex.kronecker_bijective_of_projective_homology_lt n h

/-- **The relative universal coefficient theorem with local coefficients and projective
homology**: for a local system `L` with projective fibres whose relative twisted homology modules
`Hₙ(X, A; L)` are all projective, the relative Kronecker map is bijective in every degree. -/
theorem twistedKronecker_bijective_of_projective_homology
    [∀ n, Projective (P.twistedHomology L n)] (n : ℕ) :
    Function.Bijective (P.twistedKronecker L k (M := M) n) :=
  P.twistedKronecker_bijective_of_projective_homology_lt L k M n fun _ _ ↦ inferInstance

/-- **The relative universal coefficient isomorphism with local coefficients and projective
homology**: for a local system `L` with projective fibres whose relative twisted homology modules
are all projective, the relative Kronecker map is a `k`-linear equivalence
`Hⁿ(X, A; L, M) ≃ₗ[k] (Hₙ(X, A; L) ⟶ M)`. -/
def twistedKroneckerEquivOfProjectiveHomology [∀ n, Projective (P.twistedHomology L n)] (n : ℕ) :
    P.twistedCohomology L k M n ≃ₗ[k] (P.twistedHomology L n ⟶ M) :=
  LinearEquiv.ofBijective _ (P.twistedKronecker_bijective_of_projective_homology L k M n)

/-- The equivalence `TopPair.twistedKroneckerEquivOfProjectiveHomology` is the relative Kronecker
map. -/
@[simp]
lemma twistedKroneckerEquivOfProjectiveHomology_apply [∀ n, Projective (P.twistedHomology L n)]
    (n : ℕ) (α : P.twistedCohomology L k M n) :
    P.twistedKroneckerEquivOfProjectiveHomology L k M n α = P.twistedKronecker L k n α :=
  (rfl)

end ProjectiveHomology

section HereditarySingleDegree

variable {R : Type u} [Ring R] [∀ V : ModuleCat.{max v w} R, HasProjectiveDimensionLE V 1]
  (P : TopPair.{v}) (L : LocalCoefficientSystem.{u, v, max v w} R P.fst) (k : Type*) [Ring k]
  [Linear k (ModuleCat.{max v w} R)] (M : ModuleCat.{max v w} R) [∀ x, Projective (L.obj x)]

/-- **The relative universal coefficient theorem with local coefficients above a projective
homology module**, when every `R`-module has projective dimension at most one: if `Hₙ(X, A; L)` is
projective, the relative Kronecker map `Hⁿ⁺¹(X, A; L, M) →ₗ[k] (Hₙ₊₁(X, A; L) ⟶ M)` is bijective,
for every module `M`. Nothing is assumed about the relative homology in the other degrees. -/
theorem twistedKronecker_bijective_succ_of_projective_homology (n : ℕ)
    [Projective (P.twistedHomology L n)] :
    Function.Bijective (P.twistedKronecker L k (M := M) (n + 1)) :=
  by
  rw [twistedKronecker_def]
  exact TauCeti.ChainComplex.kronecker_bijective_succ_of_projective_homology n

/-- **The relative universal coefficient isomorphism with local coefficients above a projective
homology module**, when every `R`-module has projective dimension at most one: if `Hₙ(X, A; L)` is
projective, the relative Kronecker map is a `k`-linear equivalence
`Hⁿ⁺¹(X, A; L, M) ≃ₗ[k] (Hₙ₊₁(X, A; L) ⟶ M)`. -/
def twistedKroneckerEquivSuccOfProjectiveHomology (n : ℕ)
    [Projective (P.twistedHomology L n)] :
    P.twistedCohomology L k M (n + 1) ≃ₗ[k] (P.twistedHomology L (n + 1) ⟶ M) :=
  LinearEquiv.ofBijective _ (P.twistedKronecker_bijective_succ_of_projective_homology L k M n)

/-- The equivalence `TopPair.twistedKroneckerEquivSuccOfProjectiveHomology` is the relative
Kronecker map. -/
@[simp]
lemma twistedKroneckerEquivSuccOfProjectiveHomology_apply (n : ℕ)
    [Projective (P.twistedHomology L n)] (α : P.twistedCohomology L k M (n + 1)) :
    P.twistedKroneckerEquivSuccOfProjectiveHomology L k M n α =
      P.twistedKronecker L k (n + 1) α :=
  (rfl)

/-- **Relative twisted cohomology vanishes above a projective homology module followed by a zero
one**, when every `R`-module has projective dimension at most one: if `Hₙ(X, A; L)` is projective
and `Hₙ₊₁(X, A; L) = 0`, then `Hⁿ⁺¹(X, A; L, M) = 0` for every module `M`. -/
theorem isZero_twistedCohomology_succ_of_projective_homology (n : ℕ)
    [Projective (P.twistedHomology L n)] (h : IsZero (P.twistedHomology L (n + 1))) :
    IsZero (P.twistedCohomology L k M (n + 1)) :=
  TauCeti.ChainComplex.isZero_homology_linearYonedaObj_succ_of_projective_homology n h

/-- **The splitting of the relative universal coefficient sequence with local coefficients**: a
`k`-linear right inverse `Hom(Hₙ(X, A; L), M) →ₗ[k] Hⁿ(X, A; L, M)` of the relative Kronecker map,
through a chosen retraction of the inclusion of the relative twisted cycles; it need not be natural
in the pair. -/
def twistedKroneckerSection (n : ℕ) :
    (P.twistedHomology L n ⟶ M) →ₗ[k] P.twistedCohomology L k M n :=
  TauCeti.ChainComplex.kroneckerSection k (P.twistedChainComplex L) M n

/-- `TopPair.twistedKroneckerSection` is a right inverse of the relative Kronecker map. -/
@[simp]
lemma twistedKronecker_twistedKroneckerSection (n : ℕ) (g : P.twistedHomology L n ⟶ M) :
    P.twistedKronecker L k n (P.twistedKroneckerSection L k M n g) = g :=
  by
  rw [twistedKronecker_def]
  exact TauCeti.ChainComplex.kronecker_kroneckerSection n g

/-- **Surjectivity in the relative universal coefficient sequence with local coefficients**: when
every `R`-module has projective dimension at most one, every morphism `Hₙ(X, A; L) ⟶ M` is the
evaluation of a class in `Hⁿ(X, A; L, M)`. -/
theorem twistedKronecker_surjective (n : ℕ) :
    Function.Surjective (P.twistedKronecker L k (M := M) n) :=
  by
  rw [twistedKronecker_def]
  exact TauCeti.ChainComplex.kronecker_surjective_of_isSplitMono n

end HereditarySingleDegree

section Hereditary

variable {R : Type u} [Ring R] [∀ V : ModuleCat.{max v w} R, HasProjectiveDimensionLE V 1]
  [HasExt.{t} (ModuleCat.{max v w} R)] (P : TopPair.{v})
  (L : LocalCoefficientSystem.{u, v, max v w} R P.fst) (k : Type*) [CommRing k]
  [Linear k (ModuleCat.{max v w} R)] (M : ModuleCat.{max v w} R) [∀ x, Projective (L.obj x)]

/-- **The `Ext` term of the relative universal coefficient sequence with local coefficients**,
when every `R`-module has projective dimension at most one: the `k`-linear map
`Ext¹(Hₙ(X, A; L), M) →ₗ[k] Hⁿ⁺¹(X, A; L, M)`, the algebraic map
`TauCeti.ChainComplex.extToHomology` of the relative twisted chain complex. -/
def twistedExtToCohomology (n : ℕ) :
    Ext.{t} (P.twistedHomology L n) M 1 →ₗ[k] P.twistedCohomology L k M (n + 1) :=
  TauCeti.ChainComplex.extToHomology k (P.twistedChainComplex L) M (n + 1) n

/-- The `Ext` term of the relative universal coefficient sequence with local coefficients is the
algebraic map `TauCeti.ChainComplex.extToHomology` of the relative twisted chain complex. -/
lemma twistedExtToCohomology_def (n : ℕ) :
    P.twistedExtToCohomology L k M n =
      TauCeti.ChainComplex.extToHomology k (P.twistedChainComplex L) M (n + 1) n :=
  (rfl)

/-- **The characterization of `TopPair.twistedExtToCohomology`**: the class in
`Ext¹(Hₙ(X, A; L), M)` of a morphism `β : Bₙ ⟶ M` out of the relative twisted boundaries goes to
the class of the cocycle `Cₙ₊₁(X, A; L) ⟶ Bₙ ⟶ M`. -/
lemma twistedExtToCohomology_extClass_comp_mk₀ (n : ℕ)
    (β : kernel ((P.twistedChainComplex L).homologyπ n) ⟶ M)
    (φ : (P.twistedCochainComplex L k M).cycles (n + 1))
    (hφ : (P.twistedCochainComplex L k M).iCycles (n + 1) φ =
      (P.twistedChainComplex L).toBoundaries (n + 1) n ≫ β) :
    P.twistedExtToCohomology L k M n
        ((TauCeti.kernelSequence_shortExact
          ((P.twistedChainComplex L).homologyπ n)).extClass.comp (Ext.mk₀ β) (add_zero 1)) =
      (P.twistedCochainComplex L k M).homologyπ (n + 1) φ :=
  TauCeti.ChainComplex.extToHomology_extClass_comp_mk₀ (n + 1) n β φ hφ

/-- **Injectivity in the relative universal coefficient sequence with local coefficients**: when
every `R`-module has projective dimension at most one, the map
`Ext¹(Hₙ(X, A; L), M) →ₗ[k] Hⁿ⁺¹(X, A; L, M)` is injective. -/
theorem twistedExtToCohomology_injective (n : ℕ) :
    Function.Injective (P.twistedExtToCohomology L k M n) :=
  TauCeti.ChainComplex.extToHomology_injective rfl

/-- **Exactness in the middle of the relative universal coefficient sequence with local
coefficients**: when every `R`-module has projective dimension at most one, a class in
`Hⁿ⁺¹(X, A; L, M)` evaluates to zero on `Hₙ₊₁(X, A; L)` exactly when it comes from
`Ext¹(Hₙ(X, A; L), M)`. -/
theorem exact_twistedExtToCohomology_twistedKronecker (n : ℕ) :
    Function.Exact (P.twistedExtToCohomology L k M n)
      (P.twistedKronecker L k (M := M) (n + 1)) :=
  by
  rw [twistedKronecker_def]
  exact TauCeti.ChainComplex.exact_extToHomology_kronecker rfl

/-- **The splitting of the relative universal coefficient sequence with local coefficients**, when
every `R`-module has projective dimension at most one: a `k`-linear equivalence
`Hⁿ⁺¹(X, A; L, M) ≃ₗ[k] Ext¹(Hₙ(X, A; L), M) × Hom(Hₙ₊₁(X, A; L), M)` whose second component is the
relative Kronecker map (`TopPair.twistedUniversalCoefficientEquiv_apply_snd`) and whose inverse
restricts to `TopPair.twistedExtToCohomology` on the first factor
(`TopPair.twistedUniversalCoefficientEquiv_symm_inl`). It is not natural in the pair. -/
def twistedUniversalCoefficientEquiv (n : ℕ) :
    P.twistedCohomology L k M (n + 1) ≃ₗ[k]
      Ext.{t} (P.twistedHomology L n) M 1 × (P.twistedHomology L (n + 1) ⟶ M) :=
  TauCeti.ChainComplex.universalCoefficientEquiv k (P.twistedChainComplex L) M rfl

/-- The inverse of the splitting `TopPair.twistedUniversalCoefficientEquiv` restricts to the
inclusion `TopPair.twistedExtToCohomology` of the `Ext` term on the first factor. -/
@[simp]
lemma twistedUniversalCoefficientEquiv_symm_inl (n : ℕ)
    (e : Ext.{t} (P.twistedHomology L n) M 1) :
    (P.twistedUniversalCoefficientEquiv L k M n).symm (e, 0) =
      P.twistedExtToCohomology L k M n e :=
  TauCeti.ChainComplex.universalCoefficientEquiv_symm_inl rfl e

/-- The second component of the splitting `TopPair.twistedUniversalCoefficientEquiv` is the
relative Kronecker map. -/
@[simp]
lemma twistedUniversalCoefficientEquiv_apply_snd (n : ℕ)
    (x : P.twistedCohomology L k M (n + 1)) :
    (P.twistedUniversalCoefficientEquiv L k M n x).2 = P.twistedKronecker L k (n + 1) x :=
  by
  rw [twistedKronecker_def]
  exact TauCeti.ChainComplex.universalCoefficientEquiv_apply_snd rfl x

end Hereditary

end TopPair
