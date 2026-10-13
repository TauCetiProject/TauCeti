/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.Differential.Residue
public import TauCeti.FieldTheory.FunctionField.Place.Expansion.Laurent.Derivative
import TauCeti.FieldTheory.FunctionField.ConstantExtension.ResidueField
import TauCeti.FieldTheory.FunctionField.Differential.ConstantExtension
import TauCeti.FieldTheory.FunctionField.Differential.LocalNonvanishing
import TauCeti.FieldTheory.FunctionField.Different.Separating
import TauCeti.FieldTheory.FunctionField.Place.Existence
import TauCeti.FieldTheory.FunctionField.Place.Extension.PrimeElement

/-!
# The chain rule, independence of the Kähler–Weil comparison, and the residue theorem

Let `F / k` be an algebraic function field with exact constants, and let `x` and `y` be separating
elements. The Weil differentials `dx` and `dy` (`TauCeti.weilDifferentialOfSeparating`) are the
cotraces of the canonical differential of the rational function field along `X ↦ x` and `X ↦ y`.
They satisfy the chain rule

`dy = (dy/dx) · dx`,

where `dy/dx` is the derivative of Kähler differentials (`TauCeti.derivativeOfSeparating`). This
is Stichtenoth's Theorem 4.3.2(a), `δ(y) = (dy/dx) · δ(x)`.

The proof compares one local component. At a rational place `P` where `x - a` and `y - b` are both
prime elements, the local components are residues
(`TauCeti.repartitionDualComponent_weilDifferentialOfSeparating`):
`(dy)_P (u) = res_{P,y-b} (u)` and `(dx)_P (u) = res_{P,x-a} (u)`. The transformation formula
(`TauCeti.Place.residue_eq_residue_mul_derivativeOfSeparating`) rewrites the first as
`res_{P,x-a} (u · dy/dx)`, which is the local component of `(dy/dx) · dx`. Over an exact constant
field one local component determines a Weil differential
(`TauCeti.repartitionDualComponent_inj`). Such a place exists as soon as `F` has infinitely many
rational places, for instance over an algebraically closed field
(`TauCeti.Place.infinite_setOf_degree_eq_one`): at all but finitely many rational places `P`, the
function `x - x(P)` is a prime element, since only finitely many places ramify over `k(x)`
(`TauCeti.Place.finite_setOf_forall_ord_sub_algebraMap_ne_one`).

Over a perfect constant field the chain rule holds with no condition on rational places, for
instance over a finite field. A finite separable constant field extension makes a suitable place
rational (`TauCeti.Place.exists_constantCompositum_eq_top_and_forall_degree_eq_one`), so the chain
rule holds after extending the constants. The cotrace to the extension is injective and carries
`dx` and `dy` to their counterparts
(`TauCeti.weilDifferentialCotrace_weilDifferentialOfSeparating`), while the algebra map carries
`dy/dx` to its counterpart (`TauCeti.derivativeOfSeparating_algebraMap`), so the chain rule
descends.

Consequently the Kähler–Weil comparison
`TauCeti.kaehlerDifferentialEquivWeilDifferentialOfSeparating` does not depend on the separating
element used to build it, and the local components of the Weil differential attached to a Kähler
differential `ω` are its residues: `ω_P (u) = res_P (u ω)` at every rational place with a
separating prime element (Stichtenoth, Theorem 4.3.2(d)).

Over an algebraically closed field every place is rational and every prime element is separating,
so each local component of a Weil differential at `1` is the residue there of the corresponding
Kähler differential. The abstract residue theorem `∑_P ω_P (1) = 0`
(`TauCeti.finsum_repartitionDualComponent_eq_zero`) then becomes **the residue theorem**
`∑_P res_P (ω) = 0` for every Kähler differential `ω` (Stichtenoth, Corollary 4.3.3).

## Main results

* `TauCeti.weilDifferentialOfSeparating_eq_derivativeOfSeparating_smul_of_ord_eq_one`:
  `dy = (dy/dx) · dx`, given a rational place at which `x - a` and `y - b` are prime elements.
* `TauCeti.weilDifferentialOfSeparating_eq_derivativeOfSeparating_smul`: **the chain rule
  `dy = (dy/dx) · dx`** when `F` has infinitely many rational places, and
  `TauCeti.weilDifferentialOfSeparating_eq_derivativeOfSeparating_smul_of_perfectField`, the same
  over a perfect constant field.
* `TauCeti.kaehlerDifferentialEquivWeilDifferentialOfSeparating_eq` and
  `TauCeti.kaehlerDifferentialEquivWeilDifferentialOfSeparating_eq_of_perfectField`:
  the Kähler–Weil comparison is independent of the separating element.
* `TauCeti.repartitionDualComponent_kaehlerDifferentialEquivWeilDifferentialOfSeparating`:
  **local components are residues**, `ω_P (u) = res_P (u ω)`.
* `TauCeti.Place.kaehlerResidueOfPerfectField_smul_eq_repartitionDualComponent`: the same over a
  perfect field, with the uniformizer-free residue.
* `TauCeti.finsum_kaehlerResidueOfPerfectField_eq_zero`: **the residue theorem**
  `∑_P res_P (ω) = 0` over an algebraically closed field, a sum with finitely many nonzero terms
  (`TauCeti.finite_support_kaehlerResidueOfPerfectField`).

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Theorem 4.3.2 and Corollary 4.3.3.
-/

public section

open scoped IntermediateField

open KaehlerDifferential

namespace TauCeti

variable {k F : Type*} [Field k] [Field F] [Algebra k F]

/-- **The chain rule for Weil differentials, at a common rational place** (Stichtenoth,
Theorem 4.3.2(a)): over an exact constant field, if `x - a` and `y - b` are prime elements at the
same rational place, then the Weil differentials of the separating elements `x` and `y` satisfy
`dy = (dy/dx) · dx`. -/
theorem weilDifferentialOfSeparating_eq_derivativeOfSeparating_smul_of_ord_eq_one
    (hF : IsFunctionField k F) (hex : IsIntegrallyClosedIn k F) {x y : F}
    (hx : Transcendental k x) [Algebra.IsSeparable k⟮x⟯ F]
    (hy : Transcendental k y) [Algebra.IsSeparable k⟮y⟯ F] {P : Place k F} (hP : P.degree = 1)
    {a b : k} (hxa : P.ord (x - algebraMap k F a) = 1) (hyb : P.ord (y - algebraMap k F b) = 1) :
    letI := weilDifferentialSpaceModule hF
    weilDifferentialOfSeparating hF hy =
      derivativeOfSeparating hx y • weilDifferentialOfSeparating hF hx := by
  let := weilDifferentialSpaceModule hF
  -- The translate `x - a` is separating, with the same derivative as `x`.
  have hxa' : Transcendental k (x - algebraMap k F a) := fun h ↦ hx <| by
    simpa using (h.isIntegral.add (isIntegral_algebraMap (x := a))).isAlgebraic
  have : Algebra.IsSeparable k⟮x - algebraMap k F a⟯ F := by
    rw [sub_eq_add_neg, ← map_neg, IntermediateField.adjoin_simple_add_algebraMap]
    infer_instance
  -- One local component determines a Weil differential; compare them at `P`.
  refine Subtype.ext ((repartitionDualComponent_inj hF hex (Submodule.coe_mem _)
    (Submodule.coe_mem _) P).mp (LinearMap.ext fun u ↦ ?_))
  rw [coe_weilDifferentialSpaceModule_smul, repartitionDualComponent_repartitionDualMul,
    repartitionDualComponent_weilDifferentialOfSeparating hF hy hP hyb,
    repartitionDualComponent_weilDifferentialOfSeparating hF hx hP hxa,
    P.residue_eq_residue_mul_derivativeOfSeparating hP hxa hxa' hyb,
    derivativeOfSeparating_sub_algebraMap hx hxa', map_sub, Derivation.map_algebraMap, sub_zero,
    mul_comm]

/-- **The chain rule for Weil differentials** (Stichtenoth, Theorem 4.3.2(a)): over an exact
constant field, if `F` has infinitely many rational places (for instance if `k` is algebraically
closed, `TauCeti.Place.infinite_setOf_degree_eq_one`), then the Weil differentials of any two
separating elements `x` and `y` satisfy `dy = (dy/dx) · dx`. -/
theorem weilDifferentialOfSeparating_eq_derivativeOfSeparating_smul (hF : IsFunctionField k F)
    (hex : IsIntegrallyClosedIn k F) (hinf : {P : Place k F | P.degree = 1}.Infinite) {x y : F}
    (hx : Transcendental k x) [Algebra.IsSeparable k⟮x⟯ F]
    (hy : Transcendental k y) [Algebra.IsSeparable k⟮y⟯ F] :
    letI := weilDifferentialSpaceModule hF
    weilDifferentialOfSeparating hF hy =
      derivativeOfSeparating hx y • weilDifferentialOfSeparating hF hx := by
  -- Avoid the poles and zeros of `x` and `y` and the finitely many bad places of each.
  obtain ⟨P, hP, hPgood⟩ := (hinf.sdiff (((((Place.finite_setOf_ord_ne_zero hF x).union
    (Place.finite_setOf_ord_ne_zero hF y)).union
      (Place.finite_setOf_forall_ord_sub_algebraMap_ne_one hF hx)).union
        (Place.finite_setOf_forall_ord_sub_algebraMap_ne_one hF hy)))).nonempty
  simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_and, not_forall, not_not] at hPgood
  obtain ⟨⟨⟨hx0, hy0⟩, hxP⟩, hyP⟩ := hPgood
  obtain ⟨a, hxa⟩ := hxP hP hx0.ge
  obtain ⟨b, hyb⟩ := hyP hP hy0.ge
  exact weilDifferentialOfSeparating_eq_derivativeOfSeparating_smul_of_ord_eq_one hF hex hx hy hP
    hxa hyb

/-- **The Kähler–Weil comparison does not depend on the separating element** (Stichtenoth,
Theorem 4.3.2): over an exact constant field, if `F` has infinitely many rational places, then the
comparisons built from any two separating elements are equal. -/
theorem kaehlerDifferentialEquivWeilDifferentialOfSeparating_eq
    (hF : IsFunctionField k F) (hex : IsIntegrallyClosedIn k F)
    (hinf : {P : Place k F | P.degree = 1}.Infinite) {x y : F}
    (hx : Transcendental k x) [Algebra.IsSeparable k⟮x⟯ F]
    (hy : Transcendental k y) [Algebra.IsSeparable k⟮y⟯ F] :
    kaehlerDifferentialEquivWeilDifferentialOfSeparating hF hex hx =
      kaehlerDifferentialEquivWeilDifferentialOfSeparating hF hex hy := by
  let := weilDifferentialSpaceModule hF
  -- Both are `F`-linear, so compare them on the basis `dx`.
  refine LinearEquiv.toLinearMap_injective ((kaehlerBasisOfSeparating hx).ext fun _ ↦ ?_)
  rw [kaehlerBasisOfSeparating_apply, LinearEquiv.coe_coe, LinearEquiv.coe_coe,
    kaehlerDifferentialEquivWeilDifferentialOfSeparating_D_self,
    kaehlerDifferentialEquivWeilDifferentialOfSeparating_D,
    weilDifferentialOfSeparating_eq_derivativeOfSeparating_smul hF hex hinf hy hx]

/-! ### The chain rule over a perfect field -/

section PerfectField

variable {k' F' : Type*} [Field k'] [Field F'] [Algebra k k'] [Algebra k F'] [Algebra k' F']
  [Algebra F F'] [IsScalarTower k k' F'] [IsScalarTower k F F']

/-- The descent step of the chain rule: if a finite separable constant field extension `F' = F · k'`
has a rational place `P'` lying over a place at which `q(x)` and `r(y)` are prime elements, then
`dy = (dy/dx) · dx` in `F`. -/
private theorem weilDifferentialOfSeparating_eq_derivativeOfSeparating_smul_of_constantCompositum
    [PerfectField k] [FiniteDimensional k k'] [Algebra.IsSeparable k k'] [FiniteDimensional F F']
    (h : constantCompositum F k' F' = ⊤) (hF : IsFunctionField k F)
    (hex : IsIntegrallyClosedIn k F) {x y : F}
    (hx : Transcendental k x) [Algebra.IsSeparable k⟮x⟯ F]
    (hy : Transcendental k y) [Algebra.IsSeparable k⟮y⟯ F] {P' : Place k' F'}
    (hdeg : P'.degree = 1) (hx0 : 0 ≤ (P'.restrict k F).ord x) (hy0 : 0 ≤ (P'.restrict k F).ord y)
    {q r : Polynomial k} (hq : Irreducible q) (hr : Irreducible r)
    (hqx : (P'.restrict k F).ord (Polynomial.aeval x q) = 1)
    (hry : (P'.restrict k F).ord (Polynomial.aeval y r) = 1) :
    letI := weilDifferentialSpaceModule hF
    weilDifferentialOfSeparating hF hy =
      derivativeOfSeparating hx y • weilDifferentialOfSeparating hF hx := by
  let := weilDifferentialSpaceModule hF
  have hF' : IsFunctionField k' F' := hF.of_constantCompositum_eq_top h
  have hex' : IsIntegrallyClosedIn k' F' := isIntegrallyClosedIn_of_constantCompositum_eq_top hex h
  have hx' : Transcendental k' (algebraMap F F' x) :=
    ((transcendental_algebraMap_iff (algebraMap F F').injective).mpr hx).extendScalars k'
  have hy' : Transcendental k' (algebraMap F F' y) :=
    ((transcendental_algebraMap_iff (algebraMap F F').injective).mpr hy).extendScalars k'
  have := isSeparable_adjoin_algebraMap_of_constantCompositum_eq_top (k := k) (x := x) h
  have := isSeparable_adjoin_algebraMap_of_constantCompositum_eq_top (k := k) (x := y) h
  have := isSeparable_of_constantCompositum_eq_top (k := k) h
  let := weilDifferentialSpaceModule hF'
  have he := Place.ramificationIdx_eq_one_of_constantCompositum_eq_top (k := k) h P'
  obtain ⟨a, ha⟩ := Place.exists_ord_sub_algebraMap_eq_one_of_ord_aeval_eq_one hdeg he hx0
    (PerfectField.separable_of_irreducible hq) hqx
  obtain ⟨b, hb⟩ := Place.exists_ord_sub_algebraMap_eq_one_of_ord_aeval_eq_one hdeg he hy0
    (PerfectField.separable_of_irreducible hr) hry
  have hup := weilDifferentialOfSeparating_eq_derivativeOfSeparating_smul_of_ord_eq_one hF' hex' hx'
    hy' hdeg ha hb
  refine weilDifferentialCotrace_injective (k' := k') (F' := F') hF hF' ?_
  rw [weilDifferentialCotrace_smul,
    weilDifferentialCotrace_weilDifferentialOfSeparating h hF hy,
    weilDifferentialCotrace_weilDifferentialOfSeparating h hF hx,
    ← derivativeOfSeparating_algebraMap hx hx', hup]

/-- **The chain rule for Weil differentials over a perfect field** (Stichtenoth,
Theorem 4.3.2(a)): over a perfect exact constant field, the Weil differentials of any two
separating elements `x` and `y` satisfy `dy = (dy/dx) · dx`. -/
theorem weilDifferentialOfSeparating_eq_derivativeOfSeparating_smul_of_perfectField
    [PerfectField k] (hF : IsFunctionField k F) (hex : IsIntegrallyClosedIn k F) {x y : F}
    (hx : Transcendental k x) [Algebra.IsSeparable k⟮x⟯ F]
    (hy : Transcendental k y) [Algebra.IsSeparable k⟮y⟯ F] :
    letI := weilDifferentialSpaceModule hF
    weilDifferentialOfSeparating hF hy =
      derivativeOfSeparating hx y • weilDifferentialOfSeparating hF hx := by
  have := Place.infinite hF
  -- Choose a place `P` at which `x` and `y` are units and some `q(x)` and `r(y)` are prime
  -- elements.
  obtain ⟨P, hP⟩ := (((Place.finite_setOf_forall_irreducible_ord_aeval_ne_one hF hx).union
    (Place.finite_setOf_forall_irreducible_ord_aeval_ne_one hF hy)).union
      ((Place.finite_setOf_ord_ne_zero hF x).union
        (Place.finite_setOf_ord_ne_zero hF y))).infinite_compl.nonempty
  simp only [Set.mem_compl_iff, Set.mem_union, Set.mem_ofPred_eq, not_or, not_and, not_forall,
    not_not] at hP
  obtain ⟨⟨hxq, hyq⟩, hx0, hy0⟩ := hP
  obtain ⟨q, hq, hqx⟩ := hxq hx0.ge
  obtain ⟨r, hr, hry⟩ := hyq hy0.ge
  -- Enlarge the constants until the places over `P` are rational, and pick one of them.
  have := P.finiteDimensional_residueField hF
  obtain ⟨F', k', _, _, h, hdeg⟩ :=
    Place.exists_constantCompositum_eq_top_and_forall_degree_eq_one hF hex P
  have := finiteDimensional_of_constantCompositum_eq_top (k := k) h
  obtain ⟨P', rfl⟩ := Place.restrict_surjective (hF.of_constantCompositum_eq_top h) P
  exact weilDifferentialOfSeparating_eq_derivativeOfSeparating_smul_of_constantCompositum h hF hex
    hx hy (hdeg P' rfl) hx0.ge hy0.ge hq hr hqx hry

/-- **The Kähler–Weil comparison does not depend on the separating element, over a perfect field**
(Stichtenoth, Theorem 4.3.2): over a perfect exact constant field, the comparisons built from any
two separating elements are equal. -/
theorem kaehlerDifferentialEquivWeilDifferentialOfSeparating_eq_of_perfectField [PerfectField k]
    (hF : IsFunctionField k F) (hex : IsIntegrallyClosedIn k F) {x y : F}
    (hx : Transcendental k x) [Algebra.IsSeparable k⟮x⟯ F]
    (hy : Transcendental k y) [Algebra.IsSeparable k⟮y⟯ F] :
    kaehlerDifferentialEquivWeilDifferentialOfSeparating hF hex hx =
      kaehlerDifferentialEquivWeilDifferentialOfSeparating hF hex hy := by
  let := weilDifferentialSpaceModule hF
  -- Both are `F`-linear, so compare them on the basis `dx`.
  refine LinearEquiv.toLinearMap_injective ((kaehlerBasisOfSeparating hx).ext fun _ ↦ ?_)
  rw [kaehlerBasisOfSeparating_apply, LinearEquiv.coe_coe, LinearEquiv.coe_coe,
    kaehlerDifferentialEquivWeilDifferentialOfSeparating_D_self,
    kaehlerDifferentialEquivWeilDifferentialOfSeparating_D,
    weilDifferentialOfSeparating_eq_derivativeOfSeparating_smul_of_perfectField hF hex hy hx]

end PerfectField

/-- **Local components are residues** (Stichtenoth, Theorem 4.3.2(d)): over an exact constant
field with infinitely many rational places, let `ω` be a Kähler differential and `P` a rational
place with a separating prime element `t`. The local component at `P` of the Weil differential
attached to `ω` by the Kähler–Weil comparison is `u ↦ res_P (u ω)`. -/
theorem repartitionDualComponent_kaehlerDifferentialEquivWeilDifferentialOfSeparating
    (hF : IsFunctionField k F) (hex : IsIntegrallyClosedIn k F)
    (hinf : {P : Place k F | P.degree = 1}.Infinite) {x : F}
    (hx : Transcendental k x) [Algebra.IsSeparable k⟮x⟯ F] {P : Place k F} (hP : P.degree = 1)
    {t : F} (ht : P.ord t = 1) (htr : Transcendental k t) [Algebra.IsSeparable k⟮t⟯ F]
    (ω : Ω[F⁄k]) (u : F) :
    repartitionDualComponent (kaehlerDifferentialEquivWeilDifferentialOfSeparating hF hex hx ω :
        Module.Dual k ↥(repartitionSpace k F)) P u =
      P.kaehlerResidue hP ht htr (u • ω) := by
  let := weilDifferentialSpaceModule hF
  -- Write `ω = z dt` and compute with the comparison built from `t`.
  obtain ⟨z, rfl⟩ : ∃ z : F, z • D k F t = ω :=
    ⟨(kaehlerBasisOfSeparating htr).coord () ω, by
      simpa using (kaehlerBasisOfSeparating htr).sum_repr ω⟩
  -- The residue only depends on the uniformizer, not on the proof that it is one.
  have hres {s : F} (hs : s = t) (hs₁ : P.ord s = 1) : P.residue hP hs₁ = P.residue hP ht := by
    subst hs
    rfl
  have ht₀ : P.ord (t - algebraMap k F 0) = 1 := by simpa using ht
  rw [kaehlerDifferentialEquivWeilDifferentialOfSeparating_eq hF hex hinf hx htr, map_smul,
    kaehlerDifferentialEquivWeilDifferentialOfSeparating_D_self,
    coe_weilDifferentialSpaceModule_smul, repartitionDualComponent_repartitionDualMul,
    repartitionDualComponent_weilDifferentialOfSeparating hF htr hP ht₀,
    hres (by simp) ht₀, smul_smul, Place.kaehlerResidue_smul_D, mul_comm]

/-- **Local components are residues, over a perfect field** (Stichtenoth, Theorem 4.3.2(d)): over
a perfect exact constant field with infinitely many rational places, the residue `res_P (u ω)` of a
Kähler differential at a rational place `P` is the local component at `P` of the Weil differential
attached to `ω`, evaluated at `u`. Every prime element of `P` is separating here, so no uniformizer
is needed. -/
theorem Place.kaehlerResidueOfPerfectField_smul_eq_repartitionDualComponent [PerfectField k]
    (hF : IsFunctionField k F) (hex : IsIntegrallyClosedIn k F)
    (hinf : {P : Place k F | P.degree = 1}.Infinite) {x : F}
    (hx : Transcendental k x) [Algebra.IsSeparable k⟮x⟯ F] {P : Place k F} (hP : P.degree = 1)
    (ω : Ω[F⁄k]) (u : F) :
    P.kaehlerResidueOfPerfectField hP hF (u • ω) =
      repartitionDualComponent (kaehlerDifferentialEquivWeilDifferentialOfSeparating hF hex hx ω :
        Module.Dual k ↥(repartitionSpace k F)) P u := by
  obtain ⟨t, ht, -⟩ := P.exists_ord_eq_one_and_forall_mem_ord_eq_zero ∅
  have hsep := P.transcendental_and_isSeparable_adjoin_of_ord_eq_one hF ht
  let := hsep.2
  rw [P.kaehlerResidueOfPerfectField_eq_kaehlerResidue hP ht hF hsep.1,
    repartitionDualComponent_kaehlerDifferentialEquivWeilDifferentialOfSeparating hF hex hinf hx hP
      ht hsep.1]

section IsAlgClosed

variable [IsAlgClosed k]

/-- Over an algebraically closed field, a Kähler differential has nonzero residue at only finitely
many places. -/
theorem finite_support_kaehlerResidueOfPerfectField (hF : IsFunctionField k F) (ω : Ω[F⁄k]) :
    (Function.support fun P : Place k F ↦
      P.kaehlerResidueOfPerfectField (P.degree_eq_one_of_isAlgClosed_of_isFunctionField hF) hF
        ω).Finite := by
  obtain ⟨x, hx, hsep⟩ := hF.exists_transcendental_and_isSeparable_adjoin_of_perfectField
  let := hsep
  let W :=
    kaehlerDifferentialEquivWeilDifferentialOfSeparating hF isIntegrallyClosedIn_of_isAlgClosed hx ω
  -- Each residue is the local component at `1` of the Weil differential attached to `ω`.
  convert finite_support_repartitionDualComponent_apply (Submodule.coe_mem W)
    ⟨_, const_mem_repartitionSpace hF 1⟩ using 3 with P
  rw [← one_smul F ω, Place.kaehlerResidueOfPerfectField_smul_eq_repartitionDualComponent hF
    isIntegrallyClosedIn_of_isAlgClosed (Place.infinite_setOf_degree_eq_one hF) hx]
  simp [W]

/-- **The residue theorem** (Stichtenoth, Corollary 4.3.3): over an algebraically closed field,
the residues of a Kähler differential `ω` at the places of `F` sum to zero,
`∑_P res_P (ω) = 0`. Every place is rational here, and only finitely many residues are nonzero
(`TauCeti.finite_support_kaehlerResidueOfPerfectField`).

Algebraic closure is needed: over `ℚ`, the differential `2x / (x² - 2) dx` of `ℚ(x)` has residue
zero at every rational place `x = a` and residue `-2` at infinity; the missing residue sits at the
place of `x² - 2`, which is not rational (see
`TauCeti.finsum_residue_adicOfIrreducible_X_sub_C`). -/
theorem finsum_kaehlerResidueOfPerfectField_eq_zero (hF : IsFunctionField k F) (ω : Ω[F⁄k]) :
    ∑ᶠ P : Place k F,
      P.kaehlerResidueOfPerfectField (P.degree_eq_one_of_isAlgClosed_of_isFunctionField hF) hF ω =
        0 := by
  obtain ⟨x, hx, hsep⟩ := hF.exists_transcendental_and_isSeparable_adjoin_of_perfectField
  let := hsep
  let W :=
    kaehlerDifferentialEquivWeilDifferentialOfSeparating hF isIntegrallyClosedIn_of_isAlgClosed hx ω
  -- The abstract residue theorem `∑_P W_P (1) = 0`, with each local component a residue.
  refine Eq.trans (finsum_congr fun P ↦ ?_)
    (finsum_repartitionDualComponent_eq_zero hF (Submodule.coe_mem W) 1)
  rw [← one_smul F ω, Place.kaehlerResidueOfPerfectField_smul_eq_repartitionDualComponent hF
    isIntegrallyClosedIn_of_isAlgClosed (Place.infinite_setOf_degree_eq_one hF) hx]

end IsAlgClosed

end TauCeti
