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
import TauCeti.FieldTheory.FunctionField.Differential.TraceResidue
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
differential `ω` are its residues. For the comparison built from a separating prime element `t` of
a place `P` with separable residue field this needs no hypothesis on the constants: writing
`u ω = z dt`, the local component at `u` is the trace residue `Tr_{F_P/k} res_{P,t} (z)`, the
form of Stichtenoth's Theorem 4.3.2(d) for places of arbitrary degree (Remark 4.3.7(d)). By
independence it holds for every comparison over a perfect constant field, where every residue
field is separable and every prime element separating, and at rational places it reads
`ω_P (u) = res_P (u ω)`.

These are the trace-residue formulas for Weil differentials of
`TauCeti.FieldTheory.FunctionField.Differential.TraceResidue` read through the comparison, which
preserves coordinates (`TauCeti.coord_kaehlerDifferentialEquivWeilDifferentialOfSeparating`). The
residue theorem with trace residues for Weil differentials
(`TauCeti.finsum_traceResidue_coord_eq_zero`) thereby becomes **the residue theorem** for Kähler
differentials over a perfect field: the trace residues of `ω` at all places sum to zero
(Stichtenoth, Corollary 4.3.3 and Remark 4.3.7(d)). Over an algebraically closed field every place
is rational and this is `∑_P res_P (ω) = 0`.

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
* `TauCeti.Place.traceResidue_coord_smul_eq_repartitionDualComponent`: **local components are
  trace residues** at a place of any degree with separable residue field, for the comparison built
  from a separating prime element there.
* `TauCeti.Place.traceResidue_coord_smul_eq_repartitionDualComponent_of_perfectField`: the same
  for every comparison, over a perfect constant field.
* `TauCeti.repartitionDualComponent_kaehlerDifferentialEquivWeilDifferentialOfSeparating`:
  **local components are residues**, `ω_P (u) = res_P (u ω)`, at rational places when `F` has
  infinitely many rational places.
* `TauCeti.Place.kaehlerResidueOfPerfectField_smul_eq_repartitionDualComponent`: the same over a
  perfect field, with the uniformizer-free residue.
* `TauCeti.Place.kaehlerResidue_eq_traceResidue_coord` and
  `TauCeti.Place.kaehlerResidueOfPerfectField_eq_traceResidue_coord`: at a rational place the
  residue of a Kähler differential is its trace residue.
* `TauCeti.finsum_traceResidue_kaehlerBasisOfSeparating_coord_eq_zero`: **the residue theorem**
  over a perfect field, `∑_P Tr_{F_P/k} res_{P,t_P} (ω / dt_P) = 0` for prime elements `t_P`, a
  sum with finitely many nonzero terms
  (`TauCeti.finite_support_traceResidue_kaehlerBasisOfSeparating_coord`).
* `TauCeti.finsum_kaehlerResidueOfPerfectField_eq_zero`: **the residue theorem**
  `∑_P res_P (ω) = 0` over an algebraically closed field, a sum with finitely many nonzero terms
  (`TauCeti.finite_support_kaehlerResidueOfPerfectField`).

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Theorem 4.3.2, Corollary 4.3.3 and Remark 4.3.7.
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

/-! ### Local components are residues -/

/-- **Local components are trace residues, for the comparison built from a uniformizer**
(Stichtenoth, Theorem 4.3.2(d) and Remark 4.3.7(d)): let `P` be a place of any degree whose residue
field is separable over `k`, and `t` a separating prime element of `P`. For a Kähler differential
`ω`, the trace residue `Tr_{F_P/k} res_{P,t} (u ω / dt)` is the local component at `P`, evaluated
at `u`, of the Weil differential attached to `ω` by the comparison built from `t`. No condition on
the constant field is needed beyond exactness. This is
`TauCeti.repartitionDualComponent_eq_traceResidue_coord` read through the comparison. -/
theorem Place.traceResidue_coord_smul_eq_repartitionDualComponent (hF : IsFunctionField k F)
    (hex : IsIntegrallyClosedIn k F) {P : Place k F} [Algebra.IsSeparable k P.ResidueField]
    {t : F} (ht : P.ord t = 1) (htr : Transcendental k t) [Algebra.IsSeparable k⟮t⟯ F]
    (ω : Ω[F⁄k]) (u : F) :
    P.traceResidue ht ((kaehlerBasisOfSeparating htr).coord () (u • ω)) =
      repartitionDualComponent (kaehlerDifferentialEquivWeilDifferentialOfSeparating hF hex htr ω :
        Module.Dual k ↥(repartitionSpace k F)) P u := by
  rw [repartitionDualComponent_eq_traceResidue_coord hF hex ht,
    coord_kaehlerDifferentialEquivWeilDifferentialOfSeparating, map_smul, smul_eq_mul, mul_comm]

/-- At a rational place, the residue `res_P (ω)` of a Kähler differential computed with a
separating prime element `t` is the trace residue `Tr_{F_P/k} res_{P,t} (ω / dt)`, the trace from
`F_P = k` being the identity. -/
theorem Place.kaehlerResidue_eq_traceResidue_coord {P : Place k F} (hP : P.degree = 1)
    [Algebra.IsSeparable k P.ResidueField] {t : F} (ht : P.ord t = 1) (htr : Transcendental k t)
    [Algebra.IsSeparable k⟮t⟯ F] (ω : Ω[F⁄k]) :
    P.kaehlerResidue hP ht htr ω =
      P.traceResidue ht ((kaehlerBasisOfSeparating htr).coord () ω) := by
  rw [Place.kaehlerResidue_apply, P.traceResidue_eq_residue ht hP]

/-- **Local components are residues** (Stichtenoth, Theorem 4.3.2(d)): over an exact constant
field with infinitely many rational places, let `ω` be a Kähler differential and `P` a rational
place with a separating prime element `t`. The local component at `P` of the Weil differential
attached to `ω` by the Kähler–Weil comparison is `u ↦ res_P (u ω)`. Over a perfect constant field
the hypothesis on rational places is not needed
(`TauCeti.Place.kaehlerResidueOfPerfectField_smul_eq_repartitionDualComponent`). -/
theorem repartitionDualComponent_kaehlerDifferentialEquivWeilDifferentialOfSeparating
    (hF : IsFunctionField k F) (hex : IsIntegrallyClosedIn k F)
    (hinf : {P : Place k F | P.degree = 1}.Infinite) {x : F}
    (hx : Transcendental k x) [Algebra.IsSeparable k⟮x⟯ F] {P : Place k F} (hP : P.degree = 1)
    {t : F} (ht : P.ord t = 1) (htr : Transcendental k t) [Algebra.IsSeparable k⟮t⟯ F]
    (ω : Ω[F⁄k]) (u : F) :
    repartitionDualComponent (kaehlerDifferentialEquivWeilDifferentialOfSeparating hF hex hx ω :
        Module.Dual k ↥(repartitionSpace k F)) P u =
      P.kaehlerResidue hP ht htr (u • ω) := by
  have := P.isSeparable_residueField_of_degree_eq_one hP
  rw [kaehlerDifferentialEquivWeilDifferentialOfSeparating_eq hF hex hinf hx htr,
    ← P.traceResidue_coord_smul_eq_repartitionDualComponent hF hex ht htr,
    P.kaehlerResidue_eq_traceResidue_coord hP ht htr]

section PerfectField

variable [PerfectField k]

/-- **Local components are trace residues, over a perfect field** (Stichtenoth, Theorem 4.3.2(d)
and Remark 4.3.7(d)): over a perfect exact constant field, let `ω` be a Kähler differential, `P` a
place of any degree and `t` a prime element of `P`, which is separating
(`TauCeti.Place.transcendental_and_isSeparable_adjoin_of_ord_eq_one`); the residue field of `P` is
separable over `k` (`TauCeti.Place.isSeparable_residueField_of_perfectField`). The trace residue
`Tr_{F_P/k} res_{P,t} (u ω / dt)` is the local component at `P`, evaluated at `u`, of the Weil
differential attached to `ω` by the Kähler–Weil comparison. Neither rational places nor an
algebraically closed constant field are needed; at a rational place the trace is the identity
(`TauCeti.Place.kaehlerResidueOfPerfectField_smul_eq_repartitionDualComponent`). -/
theorem Place.traceResidue_coord_smul_eq_repartitionDualComponent_of_perfectField
    (hF : IsFunctionField k F) (hex : IsIntegrallyClosedIn k F) {x : F}
    (hx : Transcendental k x) [Algebra.IsSeparable k⟮x⟯ F] {P : Place k F}
    [Algebra.IsSeparable k P.ResidueField] {t : F} (ht : P.ord t = 1) (htr : Transcendental k t)
    [Algebra.IsSeparable k⟮t⟯ F] (ω : Ω[F⁄k]) (u : F) :
    P.traceResidue ht ((kaehlerBasisOfSeparating htr).coord () (u • ω)) =
      repartitionDualComponent (kaehlerDifferentialEquivWeilDifferentialOfSeparating hF hex hx ω :
        Module.Dual k ↥(repartitionSpace k F)) P u := by
  rw [kaehlerDifferentialEquivWeilDifferentialOfSeparating_eq_of_perfectField hF hex hx htr,
    P.traceResidue_coord_smul_eq_repartitionDualComponent hF hex ht htr]

/-- Over a perfect field, the residue `res_P (ω)` of a Kähler differential at a rational place `P`
is the trace residue `Tr_{F_P/k} res_{P,t} (ω / dt)` for every prime element `t` of `P`. -/
theorem Place.kaehlerResidueOfPerfectField_eq_traceResidue_coord (hF : IsFunctionField k F)
    {P : Place k F} (hP : P.degree = 1) [Algebra.IsSeparable k P.ResidueField] {t : F}
    (ht : P.ord t = 1) (htr : Transcendental k t) [Algebra.IsSeparable k⟮t⟯ F] (ω : Ω[F⁄k]) :
    P.kaehlerResidueOfPerfectField hP hF ω =
      P.traceResidue ht ((kaehlerBasisOfSeparating htr).coord () ω) := by
  rw [P.kaehlerResidueOfPerfectField_eq_kaehlerResidue hP ht hF htr,
    P.kaehlerResidue_eq_traceResidue_coord hP ht htr]

/-- **Local components are residues, over a perfect field** (Stichtenoth, Theorem 4.3.2(d)): over
a perfect exact constant field, the residue `res_P (u ω)` of a Kähler differential at a rational
place `P` is the local component at `P` of the Weil differential attached to `ω`, evaluated at `u`.
Every prime element of `P` is separating here, so no uniformizer is needed. -/
theorem Place.kaehlerResidueOfPerfectField_smul_eq_repartitionDualComponent
    (hF : IsFunctionField k F) (hex : IsIntegrallyClosedIn k F) {x : F}
    (hx : Transcendental k x) [Algebra.IsSeparable k⟮x⟯ F] {P : Place k F} (hP : P.degree = 1)
    (ω : Ω[F⁄k]) (u : F) :
    P.kaehlerResidueOfPerfectField hP hF (u • ω) =
      repartitionDualComponent (kaehlerDifferentialEquivWeilDifferentialOfSeparating hF hex hx ω :
        Module.Dual k ↥(repartitionSpace k F)) P u := by
  obtain ⟨t, ht, -⟩ := P.exists_ord_eq_one_and_forall_mem_ord_eq_zero ∅
  obtain ⟨htr, hsep⟩ := P.transcendental_and_isSeparable_adjoin_of_ord_eq_one hF ht
  let := hsep
  have := P.isSeparable_residueField_of_degree_eq_one hP
  rw [P.kaehlerResidueOfPerfectField_eq_traceResidue_coord hF hP ht htr,
    P.traceResidue_coord_smul_eq_repartitionDualComponent_of_perfectField hF hex hx ht htr]

variable (hF : IsFunctionField k F) (hex : IsIntegrallyClosedIn k F)
  [∀ P : Place k F, Algebra.IsSeparable k P.ResidueField]
  (t : Place k F → F) (ht : ∀ P : Place k F, P.ord (t P) = 1)
  [∀ P : Place k F, Algebra.IsSeparable k⟮t P⟯ F]

include hF hex in
/-- Over a perfect field, the trace residues `Tr_{F_P/k} res_{P,t_P} (ω / dt_P)` of a Kähler
differential, computed with a prime element `t_P` at each place `P`, vanish at all but finitely
many places. The separability of each residue field over `k`
(`TauCeti.Place.isSeparable_residueField_of_perfectField`) and of `F` over each `k(t_P)`
(`TauCeti.Place.transcendental_and_isSeparable_adjoin_of_ord_eq_one`) holds automatically over a
perfect field; it is assumed only so that the trace residues and the coordinates in `dt_P` can be
stated. This is `TauCeti.finite_support_traceResidue_coord` for the Weil differential attached to
`ω`, on the constant repartition `1`. -/
theorem finite_support_traceResidue_kaehlerBasisOfSeparating_coord (ω : Ω[F⁄k]) :
    let htr : ∀ P, Transcendental k (t P) :=
      fun P ↦ P.transcendental_of_ord_ne_zero (by simp [ht P])
    (Function.support fun P : Place k F ↦
      P.traceResidue (ht P) ((kaehlerBasisOfSeparating (htr P)).coord () ω)).Finite := by
  intro htr
  obtain ⟨x, hx, hsep⟩ := hF.exists_transcendental_and_isSeparable_adjoin_of_perfectField
  let := hsep
  -- The coordinates of `ω` in `dt_P` are those of the Weil differential attached to it.
  convert finite_support_traceResidue_coord hF hex t ht
    (kaehlerDifferentialEquivWeilDifferentialOfSeparating hF hex hx ω)
    ⟨_, const_mem_repartitionSpace hF 1⟩ using 3 with P
  rw [kaehlerDifferentialEquivWeilDifferentialOfSeparating_eq_of_perfectField hF hex hx (htr P),
    coord_kaehlerDifferentialEquivWeilDifferentialOfSeparating]
  simp

include hF hex in
/-- **The residue theorem over a perfect field** (Stichtenoth, Corollary 4.3.3 and
Remark 4.3.7(d)): over a perfect exact constant field, choose a prime element `t_P` at each place
`P`. Then the trace residues of a Kähler differential `ω` sum to zero,
`∑_P Tr_{F_P/k} res_{P,t_P} (ω / dt_P) = 0`, a sum with finitely many nonzero terms
(`TauCeti.finite_support_traceResidue_kaehlerBasisOfSeparating_coord`). This is the residue
theorem for Weil differentials `TauCeti.finsum_traceResidue_coord_eq_zero` at `u = 1`, applied to
the Weil differential attached to `ω`. Unlike `TauCeti.finsum_kaehlerResidueOfPerfectField_eq_zero`,
places of every degree contribute, so this applies over finite fields. -/
theorem finsum_traceResidue_kaehlerBasisOfSeparating_coord_eq_zero (ω : Ω[F⁄k]) :
    let htr : ∀ P, Transcendental k (t P) :=
      fun P ↦ P.transcendental_of_ord_ne_zero (by simp [ht P])
    ∑ᶠ P : Place k F, P.traceResidue (ht P) ((kaehlerBasisOfSeparating (htr P)).coord () ω) =
      0 := by
  intro htr
  obtain ⟨x, hx, hsep⟩ := hF.exists_transcendental_and_isSeparable_adjoin_of_perfectField
  let := hsep
  -- The coordinates of `ω` in `dt_P` are those of the Weil differential attached to it.
  refine Eq.trans (finsum_congr fun P ↦ ?_) (finsum_traceResidue_coord_eq_zero hF hex t ht
    (kaehlerDifferentialEquivWeilDifferentialOfSeparating hF hex hx ω) 1)
  rw [kaehlerDifferentialEquivWeilDifferentialOfSeparating_eq_of_perfectField hF hex hx (htr P),
    coord_kaehlerDifferentialEquivWeilDifferentialOfSeparating, mul_one]

end PerfectField

section IsAlgClosed

variable [IsAlgClosed k]

/-- Over an algebraically closed field, the residues of a Kähler differential have finite support
and sum to zero: every place is rational, and its residue is the trace residue in any prime
element. -/
private theorem finite_support_and_finsum_kaehlerResidueOfPerfectField_eq_zero
    (hF : IsFunctionField k F) (ω : Ω[F⁄k]) :
    (Function.support fun P : Place k F ↦
      P.kaehlerResidueOfPerfectField (P.degree_eq_one_of_isAlgClosed_of_isFunctionField hF) hF
        ω).Finite ∧
    ∑ᶠ P : Place k F,
      P.kaehlerResidueOfPerfectField (P.degree_eq_one_of_isAlgClosed_of_isFunctionField hF) hF ω =
        0 := by
  choose t ht _ using fun P : Place k F ↦ P.exists_ord_eq_one_and_forall_mem_ord_eq_zero ∅
  have := fun P : Place k F ↦ (P.transcendental_and_isSeparable_adjoin_of_ord_eq_one hF (ht P)).2
  have := fun P : Place k F ↦ P.isSeparable_residueField_of_perfectField hF
  have hres := funext fun P : Place k F ↦ P.kaehlerResidueOfPerfectField_eq_traceResidue_coord hF
    (P.degree_eq_one_of_isAlgClosed_of_isFunctionField hF) (ht P)
    (P.transcendental_of_ord_ne_zero (by simp [ht P])) ω
  rw [hres]
  exact ⟨finite_support_traceResidue_kaehlerBasisOfSeparating_coord hF
    isIntegrallyClosedIn_of_isAlgClosed t ht ω,
    finsum_traceResidue_kaehlerBasisOfSeparating_coord_eq_zero hF
      isIntegrallyClosedIn_of_isAlgClosed t ht ω⟩

/-- Over an algebraically closed field, a Kähler differential has nonzero residue at only finitely
many places. -/
theorem finite_support_kaehlerResidueOfPerfectField (hF : IsFunctionField k F) (ω : Ω[F⁄k]) :
    (Function.support fun P : Place k F ↦
      P.kaehlerResidueOfPerfectField (P.degree_eq_one_of_isAlgClosed_of_isFunctionField hF) hF
        ω).Finite :=
  (finite_support_and_finsum_kaehlerResidueOfPerfectField_eq_zero hF ω).1

/-- **The residue theorem** (Stichtenoth, Corollary 4.3.3): over an algebraically closed field,
the residues of a Kähler differential `ω` at the places of `F` sum to zero,
`∑_P res_P (ω) = 0`. Every place is rational here, and only finitely many residues are nonzero
(`TauCeti.finite_support_kaehlerResidueOfPerfectField`).

Over a field that is not algebraically closed the rational places do not suffice: over `ℚ`, the
differential `2x / (x² - 2) dx` of `ℚ(x)` has residue zero at every rational place `x = a` and
residue `-2` at infinity; the missing residue sits at the place of `x² - 2`, which is not rational
(see `TauCeti.finsum_residue_adicOfIrreducible_X_sub_C`). Over a perfect field the trace residues
at the places of every degree sum to zero
(`TauCeti.finsum_traceResidue_kaehlerBasisOfSeparating_coord_eq_zero`). -/
theorem finsum_kaehlerResidueOfPerfectField_eq_zero (hF : IsFunctionField k F) (ω : Ω[F⁄k]) :
    ∑ᶠ P : Place k F,
      P.kaehlerResidueOfPerfectField (P.degree_eq_one_of_isAlgClosed_of_isFunctionField hF) hF ω =
        0 :=
  (finite_support_and_finsum_kaehlerResidueOfPerfectField_eq_zero hF ω).2

end IsAlgClosed

end TauCeti
