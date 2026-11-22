/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.ConstantExtension.Genus.Change
import TauCeti.FieldTheory.FunctionField.ConstantExtension.Genus.Stabilization
import TauCeti.FieldTheory.FunctionField.Place.Extension.PurelyInseparable
import TauCeti.FieldTheory.FunctionField.Place.OrderOfVanishing
import TauCeti.FieldTheory.IntermediateField.Adjoin.PrimitiveElement
import TauCeti.FieldTheory.PurelyInseparable.Basic
import TauCeti.FieldTheory.PurelyInseparable.Exponent
import TauCeti.LinearAlgebra.Matrix.Nonsingular.Basic
import TauCeti.RingTheory.Length.Determinant
import TauCeti.RingTheory.PowerBasis.Determinant

/-!
# Tate's genus-change theorem in positive characteristic

In characteristic `p > 0`, the genus of an algebraic function field `F / k` with exact constant
field `k` can drop under an inseparable algebraic constant field extension `F' = F · k'`, and new
constants `k'' ⊇ k'` may appear in `F'`. Tate proved in 1952 that the genus drop is constrained by
a congruence modulo `p - 1`:

`(p - 1) ∣ 2 (g(F / k) - g(F' / k''))`,

and hence `(p - 1) / 2 ∣ g(F / k) - g(F' / k'')` for every odd prime `p`. In particular, whenever
`2 g(F / k) < p - 1` (or `g(F / k) < (p - 1) / 2` for `p ≠ 2`), the genus is conserved across
every algebraic constant field extension. Both bounds are sharp: for an odd prime `p` and a
transcendental `a`, the hyperelliptic-like curve `y ^ 2 = x ^ p - a` over `𝔽_p(a)` has genus
`(p - 1) / 2` and drops to genus `0` over `𝔽_p(a ^ (1 / p))`, while for `p = 2` the curve
`y ^ 2 = x ^ 3 + a` over `𝔽_2(a)` has genus `1` and drops to genus `0` over `𝔽_2(a ^ (1 / 2))`.

Following Schröer (2009), we prove Tate's theorem without differentials by combining the global
genus-change formula `g(F / k) - 1 = [k'' : k'] (g(F' / k'') - 1) + ∑_P δ_P` from
`TauCeti.FieldTheory.FunctionField.ConstantExtension.Genus.Change` with a local determinant
computation at a purely inseparable constant step `k' / k` of prime degree `p`:

1. **Local monogenicity.** At the unique place `P'` of `F' / k'` above `P`,
   `TauCeti.Place.exists_powerBasis_integers_of_finrank_eq_prime` produces an `𝒪_P`-power basis
   `1, β, …, β ^ (p - 1)` of `𝒪_{P'}` with `β ^ p ∈ 𝒪_P`.
2. **Local singularity degree.** Writing a primitive element `α` of `k' / k` as `f(β)` for a
   polynomial `f ∈ 𝒪_P[X]` of degree `< p`, the transition matrix `A` from `1, β, …, β ^ (p - 1)`
   to `1, α, …, α ^ (p - 1)` reduces `f(X) ^ i` modulo `X ^ p - β ^ p`. Over `𝒪_{P'}`, this modulus
   factors as `(X - β) ^ p`, so `PowerBasis.det_toMatrix_aeval_pow` evaluates `det A` as
   `f'(β) ^ (p (p - 1) / 2)`. Comparing `𝒪_P`-lengths and `k`-dimensions yields
   `2 δ_P = (p - 1) · ord_{P'}(f'(β)) · deg P'`.
3. **Tower and stabilization.** In the degree-`p` step, `k'' / k'` is purely inseparable of
   `p`-power degree, so `(p - 1) ∣ [k'' : k'] - 1` and `(p - 1) ∣ 2 (g(F / k) - g(F' / k''))`.
   General algebraic constant extensions reduce to finite ones by
   `TauCeti.exists_finiteDimensional_isIntegrallyClosedIn_genus_eq`, split at the separable closure
   of `k`, and induct along prime-degree purely inseparable steps inside the exact constant field
   upstairs.

## Main results

* `TauCeti.Place.two_mul_singularityDegree_restrict_eq_of_finrank_eq_prime`,
  `TauCeti.Place.exists_two_mul_singularityDegree_restrict_eq_of_finrank_eq_prime`, and
  `TauCeti.Place.sub_one_dvd_two_mul_singularityDegree_of_finrank_eq_prime`: the local
  Tate–Schröer formula `2 δ_P = (p - 1) · ord_{P'}(f'(pb.gen)) · deg P'` and divisibility
  `(p - 1) ∣ 2 δ_P` for a purely inseparable constant extension of prime degree `p`.
* `TauCeti.sub_one_dvd_two_mul_genus_sub_genus_of_isIntegrallyClosedIn`,
  `TauCeti.sub_one_dvd_two_mul_genus_sub_genus_of_constantCompositum_eq_top`, and
  `TauCeti.sub_one_dvd_two_mul_genus_sub_genus_algebraicClosure_of_constantCompositum_eq_top`:
  Tate's genus-change divisibility `(p - 1) ∣ 2 (g(F / k) - g(F' / k''))` for arbitrary algebraic
  constant extensions in characteristic `p`, with or without constant growth.
* `TauCeti.sub_one_div_two_dvd_genus_sub_genus_of_constantCompositum_eq_top`: for `p ≠ 2`,
  `(p - 1) / 2 ∣ g(F / k) - g(F' / k'')`.
* `TauCeti.genus_eq_genus_of_two_mul_genus_lt_sub_one`,
  `TauCeti.genus_eq_genus_of_genus_lt_sub_one_div_two`, and
  `TauCeti.isIntegrallyClosedIn_of_one_le_genus_of_two_mul_genus_lt_sub_one`: genus conservation
  and preservation of exact constants when `2 g(F / k) < p - 1`.

## References

* J. Tate, *Genus change in inseparable extensions of function fields*, Proc. Amer. Math. Soc. 3
  (1952), 400–406.
* S. Schröer, *On genus change in algebraic curves over imperfect fields*, Proc. Amer. Math. Soc.
  137 (2009), 1239–1243.
-/

public section

open IntermediateField IsLocalRing Module Polynomial

namespace TauCeti

universe u u' v v'

/-! ### The local Tate–Schröer formula -/

section LocalFormula

variable {k : Type u} {k' : Type u'} {F : Type v} {F' : Type v'}
variable [Field k] [Field k'] [Field F] [Field F']
variable [Algebra k k'] [Algebra k F] [Algebra k F'] [Algebra k' F'] [Algebra F F']
variable [IsScalarTower k k' F'] [IsScalarTower k F F']

attribute [local instance 10] Place.algebraIntegersExtension Place.isScalarTowerIntegersExtension

/-- Comparing `𝒪_P`-length and `k'`-dimension identifies `p · δ_P` with `ord_P(det A) · deg P`. -/
private theorem Place.mul_singularityDegree_eq_toNat_ord_det_mul_degree {n p : ℕ} (hp : p.Prime)
    [FiniteDimensional k k'] [IsPurelyInseparable F F'] (hk' : finrank k k' = p)
    (hF : IsFunctionField k F) (hex : IsIntegrallyClosedIn k F)
    (h : constantCompositum F k' F' = ⊤) (P' : Place k' F') (hnp : n = p)
    (w : Basis (Fin n) (P'.restrict k F).integers P'.integers) {α : k'} (hα : k⟮α⟯ = ⊤) :
    let αS : P'.integers := ⟨algebraMap k' F' α, P'.algebraMap_mem_integers α⟩
    let ψ := w.constr (P'.restrict k F).integers fun i : Fin n ↦ αS ^ (i : ℕ)
    let A := LinearMap.toMatrix w w ψ
    (A.det : F) ≠ 0 ∧
      p * (P'.restrict k F).singularityDegree k' F' =
        ((P'.restrict k F).ord (A.det : F)).toNat * (P'.restrict k F).degree := by
  classical
  have := finiteDimensional_of_constantCompositum_eq_top (k := k) h
  have hF' := hF.of_constantCompositum_eq_top h
  have hn : finrank F F' = finrank k k' := by
    have hdeg := finrank_constantCompositum_eq_finrank_of_finrank_prime F k' F' hex (hk' ▸ hp)
    rwa [h, IntermediateField.finrank_top'] at hdeg
  set P := P'.restrict k F
  let αS : P'.integers := ⟨algebraMap k' F' α, P'.algebraMap_mem_integers α⟩
  let ψ := w.constr P.integers fun i : Fin n ↦ αS ^ (i : ℕ)
  let A := LinearMap.toMatrix w w ψ
  let pbk : PowerBasis k k' :=
    PowerBasis.ofAdjoinSimpleEqTop (Algebra.IsIntegral.isIntegral α) hα
  have hpbk_dim : pbk.dim = n := (pbk.finrank.symm.trans hk').trans hnp.symm
  let bk : Basis (Fin n) k k' := pbk.basis.reindex (finCongr hpbk_dim)
  have hbk (i : Fin n) : bk i = α ^ (i : ℕ) := by simp [bk, pbk]
  let cF : Basis (Fin n) F F' := constantBasisOfFinrankEq h hn bk
  have hcF (i : Fin n) : cF i = (ψ (w i) : F') := by
    rw [constantBasisOfFinrankEq_apply, hbk, map_pow, w.constr_basis]
    rfl
  let ιP : P'.integers →ₛₗ[algebraMap P.integers F] F' :=
    { toFun := Subtype.val
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun r x ↦ by
        rw [Algebra.smul_def, Algebra.smul_def, Subring.coe_mul, Place.coe_algebraMap_integers,
          ValuationSubring.algebraMap_apply] }
  have hli : LinearIndependent F fun i ↦ ιP (ψ (w i)) :=
    (funext fun i ↦ (hcF i).symm : (fun i ↦ ιP (ψ (w i))) = cF) ▸ cF.linearIndependent
  have hAdet : A.det ≠ 0 := LinearMap.det_toMatrix_ne_zero_of_linearIndependent w w ψ ιP hli
  have hAdetF : (A.det : F) ≠ 0 :=
    LinearMap.map_det_toMatrix_ne_zero_of_linearIndependent w w ψ ιP hli
  have hrange : LinearMap.range ψ = P'.constantSpanSubmodule k F := by
    rw [LinearMap.range_eq_map, ← w.span_eq, Submodule.map_span, ← Set.range_comp,
      P'.constantSpanSubmodule_eq_span h hn bk]
    refine congrArg (Submodule.span P.integers) (congrArg Set.range (funext fun i ↦ ?_))
    rw [Function.comp_apply, w.constr_basis]
    exact Subtype.ext (by simp [αS, hbk])
  let _ := Place.integersAlgebraBase k P'
  have := Place.isScalarTower_integersAlgebraBase k P'
  have := Place.isScalarTower_integers_restrict k F P'
  have hord : Ring.ord P.integers A.det = ((P.ord (A.det : F)).toNat : ℕ∞) :=
    P.ringOrd_integers_eq_toNat_ord hAdetF
  have hlen : (Module.length P.integers (P'.integers ⧸ P'.constantSpanSubmodule k F)).toNat =
      (P.ord (A.det : F)).toNat := by
    rw [← hrange, w.length_quotient_range_eq_length_quotient_range_toMatrix ψ,
      Matrix.length_quotient_range_mulVecLin_eq_ord_det A hAdet, hord, ENat.toNat_natCast]
  have hfinrank_k : p * P.singularityDegree k' F' = finrank k (P.singularityQuotient k' F') := by
    rw [← hk', Place.singularityDegree_def k' F' P,
      Module.finrank_mul_finrank k k' (P.singularityQuotient k' F')]
  refine ⟨hAdetF, ?_⟩
  rw [hfinrank_k, ← (P'.singularityQuotientLinearEquiv k F hF').finrank_eq,
    TauCeti.finrank_eq_length_mul_finrank_residueField k P.integers
      (P'.integers ⧸ P'.constantSpanSubmodule k F), hlen, P.degree_eq_finrank]

/-- Triangular-exponent arithmetic translating `det A = dS ^ (p (p - 1) / 2)` into
`2 e(P' ∣ P) ord_P(det A) = p (p - 1) ord_{P'}(dS)`. -/
private theorem Place.two_mul_ramificationIdx_mul_toNat_ord_eq {p : ℕ}
    [Algebra.IsIntegral F F'] (P' : Place k' F') {x : (P'.restrict k F).integers}
    {d : P'.integers} (hxd : algebraMap (P'.restrict k F).integers P'.integers x =
      d ^ (p * (p - 1) / 2)) :
    2 * Place.ramificationIdx F P' * ((P'.restrict k F).ord (x : F)).toNat =
      p * (p - 1) * (P'.ord (d : F')).toNat := by
  have h := Place.ramificationIdx_mul_toNat_ord_eq_of_algebraMap_eq_pow k F P'
    x.property d.property (congrArg Subtype.val hxd)
  have h2 : 2 * (p * (p - 1) / 2) = p * (p - 1) :=
    Nat.mul_div_cancel' (Nat.even_mul_pred_self p).two_dvd
  calc 2 * Place.ramificationIdx F P' * ((P'.restrict k F).ord (x : F)).toNat
      = 2 * (Place.ramificationIdx F P' * ((P'.restrict k F).ord (x : F)).toNat) := by ring
    _ = 2 * (p * (p - 1) / 2) * (P'.ord (d : F')).toNat := by rw [h]; ring
    _ = p * (p - 1) * (P'.ord (d : F')).toNat := by rw [h2]

/-- **Local Tate–Schröer formula**: for a purely inseparable constant field extension `F' = F · k'`
of prime degree `p` over a function field `F / k` with exact constants, given an `𝒪_P`-power
basis `pb` of `𝒪_{P'}` at the unique place `P'` above `P = P'|_F` and a primitive element `α`
of `k' / k` represented as `f(pb.gen)` with `f ∈ 𝒪_P[X]`, we have
`2 δ_P = (p - 1) · ord_{P'}(f'(pb.gen)) · deg P'`. -/
theorem Place.two_mul_singularityDegree_restrict_eq_of_finrank_eq_prime {p : ℕ}
    [Fact p.Prime] [IsPurelyInseparable k k'] [Algebra.IsIntegral F F']
    (hk' : finrank k k' = p) (hF : IsFunctionField k F) (hex : IsIntegrallyClosedIn k F)
    (h : constantCompositum F k' F' = ⊤) (P' : Place k' F')
    (pb : PowerBasis (P'.restrict k F).integers P'.integers) {α : k'} (hα : k⟮α⟯ = ⊤)
    {f : Polynomial (P'.restrict k F).integers}
    (hf : (aeval pb.gen f : F') = algebraMap k' F' α) :
    2 * (P'.restrict k F).singularityDegree k' F' =
      (p - 1) * (P'.ord (aeval pb.gen f.derivative : P'.integers)).toNat * P'.degree := by
  classical
  have hp : p.Prime := Fact.out
  have : FiniteDimensional k k' := Module.finite_of_finrank_pos (hk' ▸ hp.pos)
  have : CharP k p :=
    TauCeti.IsPurelyInseparable.charP_of_prime_dvd_finrank (K := k) (M := k') hp (by rw [hk'])
  have := finiteDimensional_of_constantCompositum_eq_top (k := k) h
  have : IsPurelyInseparable F F' := isPurelyInseparable_of_constantCompositum_eq_top (k := k) h
  have hFF' : finrank F F' = p := by
    have hdeg := finrank_constantCompositum_eq_finrank_of_finrank_prime F k' F' hex (hk' ▸ hp)
    rwa [h, IntermediateField.finrank_top', hk'] at hdeg
  have hdim : pb.dim = p := by
    rw [← PowerBasis.finrank,
      ← IsFractionRing.finrank_eq (P'.restrict k F).integers F P'.integers F', hFF']
  have : CharP F p := charP_of_injective_algebraMap (algebraMap k F).injective p
  have : ExpChar F p := .prime hp
  have : CharP k' p := charP_of_injective_algebraMap (algebraMap k k').injective p
  have : CharP P'.integers p :=
    charP_of_injective_algebraMap (algebraMap k' P'.integers).injective p
  obtain ⟨b₀, hb₀⟩ := TauCeti.IsPurelyInseparable.pow_mem_of_finrank_le_pow F F' p (n := 1)
    (by simp [hFF']) (pb.gen : F')
  rw [pow_one] at hb₀
  let b : (P'.restrict k F).integers :=
    ⟨b₀, (Place.mem_integers_iff_of_algebraMap_eq_pow k F P' hp.ne_zero hb₀).1 pb.gen.property⟩
  have hb : algebraMap (P'.restrict k F).integers P'.integers b = pb.gen ^ pb.dim := by
    rw [hdim]
    exact Subtype.ext hb₀
  have hfdet := (pb.det_toMatrix_aeval_pow (p := p) (e := 1) (by rw [hdim, pow_one]) hb f).trans
    (by rw [hdim])
  have hf_int : aeval pb.gen f = ⟨algebraMap k' F' α, P'.algebraMap_mem_integers α⟩ :=
    Subtype.ext hf
  rw [hf_int] at hfdet
  obtain ⟨-, hlen⟩ := P'.mul_singularityDegree_eq_toNat_ord_det_mul_degree hp hk' hF hex h hdim
    pb.basis hα
  have hord_eq := P'.two_mul_ramificationIdx_mul_toNat_ord_eq hfdet
  have hef : Place.ramificationIdx F P' * Place.relativeDegree k F P' = p :=
    (Place.ramificationIdx_mul_relativeDegree_eq_finrank_of_isPurelyInseparable k F hF P').trans
      hFF'
  have hfdeg : Place.relativeDegree k F P' * (P'.restrict k F).degree = p * P'.degree := by
    simpa [hk'] using (Place.finrank_mul_degree_eq_relativeDegree_mul_degree_restrict k F P').symm
  refine Nat.mul_left_cancel (Nat.mul_pos hp.pos hp.pos) ?_
  calc p * p * (2 * (P'.restrict k F).singularityDegree k' F')
      = 2 * (Place.ramificationIdx F P' * Place.relativeDegree k F P') *
          (p * (P'.restrict k F).singularityDegree k' F') := by rw [hef]; ring
    _ = (2 * Place.ramificationIdx F P' * ((P'.restrict k F).ord _).toNat) *
          (Place.relativeDegree k F P' * (P'.restrict k F).degree) := by rw [hlen]; ring
    _ = (p * (p - 1) * (P'.ord (aeval pb.gen f.derivative : P'.integers)).toNat) *
          (p * P'.degree) := by rw [hord_eq, hfdeg]
    _ = p * p * ((p - 1) * (P'.ord (aeval pb.gen f.derivative : P'.integers)).toNat *
          P'.degree) := by ring

/-- **Local Tate–Schröer formula** (existential form): for a purely inseparable constant field
extension `F' = F · k'` of prime degree `p` over a function field `F / k` with exact constants, at
the unique place `P'` above `P = P'|_F` there is a natural number `m` such that
`2 δ_P = (p - 1) · m · deg P'`. -/
theorem Place.exists_two_mul_singularityDegree_restrict_eq_of_finrank_eq_prime {p : ℕ}
    [Fact p.Prime] [IsPurelyInseparable k k'] [Algebra.IsIntegral F F']
    (hk' : finrank k k' = p) (hF : IsFunctionField k F) (hex : IsIntegrallyClosedIn k F)
    (h : constantCompositum F k' F' = ⊤) (P' : Place k' F') :
    ∃ m : ℕ, 2 * (P'.restrict k F).singularityDegree k' F' = (p - 1) * m * P'.degree := by
  have hp : p.Prime := Fact.out
  have : FiniteDimensional k k' := Module.finite_of_finrank_pos (hk' ▸ hp.pos)
  have := finiteDimensional_of_constantCompositum_eq_top (k := k) h
  have : IsPurelyInseparable F F' := isPurelyInseparable_of_constantCompositum_eq_top (k := k) h
  have hFF' : finrank F F' = p := by
    have hdeg := finrank_constantCompositum_eq_finrank_of_finrank_prime F k' F' hex (hk' ▸ hp)
    rwa [h, IntermediateField.finrank_top', hk'] at hdeg
  obtain ⟨pb, -⟩ :=
    P'.exists_powerBasis_integers_of_finrank_eq_prime hF (hF.of_constantCompositum_eq_top h) hFF'
  obtain ⟨α, hα⟩ := Field.exists_adjoin_simple_eq_top_of_finrank_prime (hk' ▸ hp)
  obtain ⟨f, hf⟩ := pb.exists_eq_aeval' ⟨algebraMap k' F' α, P'.algebraMap_mem_integers α⟩
  exact ⟨(P'.ord (aeval pb.gen f.derivative : P'.integers)).toNat,
    P'.two_mul_singularityDegree_restrict_eq_of_finrank_eq_prime hk' hF hex h pb hα
      (congrArg Subtype.val hf).symm⟩

/-- **Local Tate divisibility**: in a purely inseparable constant field extension `F' = F · k'` of
prime degree `p` over a function field `F / k` with exact constants, `p - 1` divides `2 δ_P` at
every place `P` of `F / k`. -/
theorem Place.sub_one_dvd_two_mul_singularityDegree_of_finrank_eq_prime {p : ℕ} [Fact p.Prime]
    [IsPurelyInseparable k k'] (hk' : finrank k k' = p) (hF : IsFunctionField k F)
    (hex : IsIntegrallyClosedIn k F) (h : constantCompositum F k' F' = ⊤) (P : Place k F) :
    (p - 1) ∣ 2 * P.singularityDegree k' F' := by
  have hp : p.Prime := Fact.out
  have : FiniteDimensional k k' := Module.finite_of_finrank_pos (hk' ▸ hp.pos)
  have := finiteDimensional_of_constantCompositum_eq_top (k := k) h
  obtain ⟨P', rfl⟩ := Place.restrict_surjective (hF.of_constantCompositum_eq_top h) P
  obtain ⟨m, hm⟩ := P'.exists_two_mul_singularityDegree_restrict_eq_of_finrank_eq_prime hk' hF hex h
  exact ⟨m * P'.degree, by rw [hm, mul_assoc]⟩

/-- For an odd prime `p`, `(p - 1) / 2` divides the local singularity degree `δ_P` at every place
`P` of a function field `F / k` with exact constants under a degree-`p` purely inseparable constant
field extension `F' = F · k'`. -/
theorem Place.sub_one_div_two_dvd_singularityDegree_of_finrank_eq_prime {p : ℕ} [Fact p.Prime]
    [IsPurelyInseparable k k'] (hp2 : p ≠ 2) (hk' : finrank k k' = p)
    (hF : IsFunctionField k F) (hex : IsIntegrallyClosedIn k F)
    (h : constantCompositum F k' F' = ⊤) (P : Place k F) :
    ((p - 1) / 2) ∣ P.singularityDegree k' F' := by
  have hp : p.Prime := Fact.out
  have h2 : 2 * ((p - 1) / 2) = p - 1 :=
    Nat.mul_div_cancel' ((hp.odd_of_ne_two hp2).tsub_odd odd_one).two_dvd
  refine (Nat.mul_dvd_mul_iff_left two_pos).1 ?_
  rw [h2]
  exact P.sub_one_dvd_two_mul_singularityDegree_of_finrank_eq_prime hk' hF hex h

end LocalFormula

/-! ### Tate's genus-change theorem -/

section Tate

/-- Tate's genus-change divisibility for a single purely inseparable constant step of prime degree
`p`, allowing constant growth into an exact constant field `k''` of `F'`. -/
private theorem sub_one_dvd_two_mul_genus_sub_genus_of_finrank_eq_prime {k : Type u}
    {k' : Type u'} {F : Type v} {F' : Type v'} [Field k] [Field k'] [Field F] [Field F']
    [Algebra k k'] [Algebra k F] [Algebra k F'] [Algebra k' F'] [Algebra F F']
    [IsScalarTower k k' F'] [IsScalarTower k F F'] {p : ℕ} [Fact p.Prime] [CharP k p]
    [IsPurelyInseparable k k'] (hk' : finrank k k' = p) (hF : IsFunctionField k F)
    (hex : IsIntegrallyClosedIn k F) (h : constantCompositum F k' F' = ⊤)
    {k'' : Type*} [Field k''] [Algebra k' k''] [Algebra k'' F'] [IsScalarTower k' k'' F']
    [Algebra.IsAlgebraic k' k''] (hex'' : IsIntegrallyClosedIn k'' F') :
    genus k'' F' ≤ genus k F ∧ (p - 1) ∣ 2 * (genus k F - genus k'' F') := by
  have hp : p.Prime := Fact.out
  have : FiniteDimensional k k' := Module.finite_of_finrank_pos (hk' ▸ hp.pos)
  have hFF' : finrank F F' = p := by
    have hdeg := finrank_constantCompositum_eq_finrank_of_finrank_prime F k' F' hex (hk' ▸ hp)
    rwa [h, IntermediateField.finrank_top', hk'] at hdeg
  have hn : finrank F F' = finrank k k' := hFF'.trans hk'.symm
  have hF' := hF.of_constantCompositum_eq_top h
  have : FiniteDimensional k' k'' := hF'.finiteDimensional_of_isAlgebraic k''
  have : IsPurelyInseparable F F' := isPurelyInseparable_of_constantCompositum_eq_top (k := k) h
  have : CharP k' p := charP_of_injective_algebraMap (algebraMap k k').injective p
  have : ExpChar k' p := .prime hp
  have : IsPurelyInseparable k' k'' :=
    isPurelyInseparable_enlargement_of_finrank_eq_prime hp hex hFF' (k'' := k'')
  obtain ⟨m, hm⟩ := IsPurelyInseparable.finrank_eq_pow k' k'' p
  have hfin := finite_setOf_singularityDegree_ne_zero hF hex h hn
  have heq := genus_sub_one_eq_finrank_mul_genus_sub_one_add_finsum_singularityDegree
    hF hex h hn hex''
  have hsupp : (Function.support fun P : Place k F ↦ (P.singularityDegree k' F' : ℤ)) ⊆
      hfin.toFinset := fun P hP ↦ by simpa [Function.mem_support] using hP
  rw [finsum_eq_sum_of_support_subset _ hsupp] at heq
  have hgle : genus k'' F' ≤ genus k F := by
    have hm1 : (1 : ℤ) ≤ finrank k' k'' := by exact_mod_cast (finrank_pos (R := k') (M := k''))
    have hsum : (0 : ℤ) ≤ ∑ P ∈ hfin.toFinset, (P.singularityDegree k' F' : ℤ) :=
      Finset.sum_nonneg fun _ _ ↦ Nat.cast_nonneg _
    by_cases hg0 : genus k'' F' = 0 <;> [omega; nlinarith]
  have hid : (2 * ((genus k F : ℤ) - genus k'' F') : ℤ) =
      2 * ((finrank k' k'' : ℤ) - 1) * ((genus k'' F' : ℤ) - 1) +
        ∑ P ∈ hfin.toFinset, (2 * (P.singularityDegree k' F' : ℤ)) := by
    rw [← Finset.mul_sum]; linarith
  have hp1 : 1 ≤ p := hp.pos
  have hdvd_z : ((p : ℤ) - 1) ∣ 2 * ((genus k F : ℤ) - genus k'' F') := by
    rw [hid]
    refine dvd_add ?_ (Finset.dvd_sum fun P _ ↦ ?_)
    · rw [hm, Nat.cast_pow]
      exact (dvd_mul_of_dvd_right (by simpa using sub_dvd_pow_sub_pow (p : ℤ) 1 m) 2).mul_right _
    · have hdvdP := Int.natCast_dvd_natCast.2
        (P.sub_one_dvd_two_mul_singularityDegree_of_finrank_eq_prime hk' hF hex h)
      rwa [Nat.cast_sub hp1, Nat.cast_one, Nat.cast_mul, Nat.cast_ofNat] at hdvdP
  refine ⟨hgle, (Int.natCast_dvd_natCast.1 ?_)⟩
  simpa [hp1, hgle] using hdvd_z

/-- Single prime-step decomposition inside a nontrivial finite purely inseparable constant
extension `K → M` with exact constants on both sides: given an intermediate field `L` of degree `p`
over `K`, cutting out `L₁ = (E · L) ∩ M` as an intermediate field over `L` produces a strict
subextension `L₁ → M` with exact constants in `E · L` whose genus drop from `E / K` satisfies
Tate's divisibility. -/
private theorem exists_step_of_finrank_eq_prime {K M : Type u'} {E F' : Type v'} [Field K]
    [Field M] [Field E] [Field F'] [Algebra K M] [Algebra K E] [Algebra K F'] [Algebra M F']
    [Algebra E F'] [IsScalarTower K M F'] [IsScalarTower K E F'] {p : ℕ} [Fact p.Prime] [CharP K p]
    [IsPurelyInseparable K M] [FiniteDimensional K M] (L : IntermediateField K M)
    (hL : finrank K L = p) (hE : IsFunctionField K E) (hexK : IsIntegrallyClosedIn K E)
    (hEM : constantCompositum E M F' = ⊤) (hexM : IsIntegrallyClosedIn M F') :
    ∃ (L₁ : IntermediateField L M) (EL : Type v') (_ : Field EL) (_ : Algebra L₁ EL)
      (_ : Algebra EL F') (_ : IsScalarTower L₁ EL F'),
      finrank L₁ M < finrank K M ∧ IsFunctionField L₁ EL ∧ IsIntegrallyClosedIn L₁ EL ∧
        constantCompositum EL M F' = ⊤ ∧ genus L₁ EL ≤ genus K E ∧
        (p - 1) ∣ 2 * (genus K E - genus L₁ EL) := by
  let EL := constantCompositum E L F'
  let _ := constantCompositumAlgebra E L F'
  have := isScalarTower_constantCompositum E L F'
  have := isScalarTower_base_constantCompositum K E L F'
  have hEL : constantCompositum E L EL = ⊤ := (constantCompositum_eq_top_iff E L F' EL).2 rfl
  let L₀ : IntermediateField K M := (EL.restrictScalars K).comap (IsScalarTower.toAlgHom K M F')
  have hmemL₀ (m : M) : m ∈ L₀ ↔ algebraMap M F' m ∈ EL := Iff.rfl
  have hLL₀ : L ≤ L₀ := fun m hm ↦ (hmemL₀ m).2 <| by
    have hmem := algebraMap_mem_constantCompositum E L F' ⟨m, hm⟩
    rwa [IsScalarTower.algebraMap_apply L M F', IntermediateField.algebraMap_apply] at hmem
  let L₁ : IntermediateField L M := IntermediateField.extendScalars hLL₀
  have hmEL (m : L₁) : algebraMap L₁ F' m ∈ EL := by
    rw [IsScalarTower.algebraMap_apply L₁ M F', IntermediateField.algebraMap_apply]
    exact (hmemL₀ (m : M)).1 ((IntermediateField.mem_extendScalars hLL₀).1 m.property)
  let _ : Algebra L₁ EL := ((algebraMap L₁ F').codRestrict EL hmEL).toAlgebra
  have hst : IsScalarTower L₁ EL F' := .of_algebraMap_eq fun m ↦ by
    rw [IntermediateField.algebraMap_apply, RingHom.algebraMap_toAlgebra, RingHom.codRestrict_apply]
  have : IsScalarTower L L₁ EL := .of_algebraMap_eq fun c ↦ (algebraMap EL F').injective <| by
    rw [← IsScalarTower.algebraMap_apply L EL F', ← IsScalarTower.algebraMap_apply L₁ EL F',
      ← IsScalarTower.algebraMap_apply L L₁ F']
  have : FiniteDimensional L M := FiniteDimensional.right K L M
  have : FiniteDimensional L L₁ := FiniteDimensional.left L L₁ M
  have : FiniteDimensional L₁ M := FiniteDimensional.right L L₁ M
  have hexL₁ : IsIntegrallyClosedIn L₁ EL :=
    isIntegrallyClosedIn_iff.2 ⟨(algebraMap L₁ EL).injective, fun {y} hy ↦ by
      have hyM : IsIntegral M (y : F') := (hy.map (IsScalarTower.toAlgHom L₁ EL F')).tower_top
      obtain ⟨m, hm⟩ := IsIntegrallyClosedIn.isIntegral_iff.1 hyM
      have hm₀ : m ∈ L₀ := (hmemL₀ m).2 (hm.symm ▸ y.property)
      refine ⟨⟨m, (IntermediateField.mem_extendScalars hLL₀).2 hm₀⟩, Subtype.ext ?_⟩
      rw [RingHom.algebraMap_toAlgebra, RingHom.codRestrict_apply,
        IsScalarTower.algebraMap_apply L₁ M F', IntermediateField.algebraMap_apply]
      exact hm⟩
  obtain ⟨hgle₁, hdvd₁⟩ :=
    sub_one_dvd_two_mul_genus_sub_genus_of_finrank_eq_prime hL hE hexK hEL (k'' := L₁) hexL₁
  have hlt : finrank L₁ M < finrank K M := by
    have h1 := finrank_mul_finrank K L M
    have h2 := finrank_mul_finrank L L₁ M
    have hp : p.Prime := Fact.out
    have := hp.one_lt
    have : 0 < finrank L L₁ := finrank_pos
    have : 0 < finrank L₁ M := finrank_pos
    nlinarith
  exact ⟨L₁, EL, inferInstance, inferInstance, inferInstance, hst, hlt,
    (hE.of_constantCompositum_eq_top hEL).of_isAlgebraic, hexL₁,
    constantCompositum_eq_top_of_eq_top E M F' EL hEM, hgle₁, hdvd₁⟩

/-- Induction over finite purely inseparable constant extensions with exact constants on both
sides, stepping along intermediate fields of prime degree `p`. -/
private theorem sub_one_dvd_two_mul_genus_sub_genus_of_isPurelyInseparable_of_finite (p : ℕ)
    [Fact p.Prime] (n : ℕ) :
    ∀ (K M : Type u') (E F' : Type v') [Field K] [Field M] [Field E] [Field F'] [Algebra K M]
      [Algebra K E] [Algebra K F'] [Algebra M F'] [Algebra E F'] [IsScalarTower K M F']
      [IsScalarTower K E F'] [CharP K p] [IsPurelyInseparable K M] [FiniteDimensional K M],
      finrank K M = n → IsFunctionField K E → IsIntegrallyClosedIn K E →
      constantCompositum E M F' = ⊤ → IsIntegrallyClosedIn M F' →
      (p - 1) ∣ 2 * (genus K E - genus M F') := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro K M E F' _ _ _ _ _ _ _ _ _ _ _ _ _ _ hn hE hexK hEM hexM
  by_cases hsurj : Function.Surjective (algebraMap K M)
  · have hbij : Function.Bijective (algebraMap K M) := ⟨(algebraMap K M).injective, hsurj⟩
    have : Algebra.IsSeparable K M :=
      AlgEquiv.Algebra.isSeparable (AlgEquiv.ofBijective (Algebra.ofId K M) hbij)
    rw [genus_eq_genus_of_constantCompositum_eq_top hE hexK hEM, Nat.sub_self, mul_zero]
    exact dvd_zero _
  · obtain ⟨L, hL⟩ :=
      TauCeti.IsPurelyInseparable.exists_intermediateField_finrank_eq_expChar p hsurj
    obtain ⟨L₁, EL, _, _, _, _, hlt, hFEL₁, hexL₁, hELM_top, hgle₁, hdvd₁⟩ :=
      exists_step_of_finrank_eq_prime L hL hE hexK hEM hexM
    have : CharP L p := charP_of_injective_algebraMap (algebraMap K L).injective p
    have : CharP L₁ p := charP_of_injective_algebraMap (algebraMap L L₁).injective p
    have : IsPurelyInseparable L M := IsPurelyInseparable.tower_top K L M
    have : IsPurelyInseparable L₁ M := IsPurelyInseparable.tower_top L L₁ M
    have : FiniteDimensional L M := FiniteDimensional.right K L M
    have : FiniteDimensional L₁ M := FiniteDimensional.right L L₁ M
    have hdvd₂ := ih _ (hn ▸ hlt) L₁ M EL F' rfl hFEL₁ hexL₁ hELM_top hexM
    have hgle₂ : genus M F' ≤ genus L₁ EL :=
      genus_le_genus_of_constantCompositum_eq_top hFEL₁ hELM_top
    have hsplit : 2 * (genus K E - genus M F') =
        2 * (genus K E - genus L₁ EL) + 2 * (genus L₁ EL - genus M F') := by omega
    rw [hsplit]
    exact dvd_add hdvd₁ hdvd₂

/-- Tate's genus-change divisibility for a finite algebraic constant field extension with exact
constants on both sides, splitting `k → M` at the separable closure of `k` in `M`. -/
private theorem sub_one_dvd_two_mul_genus_sub_genus_of_finite_of_isIntegrallyClosedIn
    {k : Type u} {M : Type u'} {F : Type v} {FM : Type v'} [Field k] [Field M] [Field F]
    [Field FM] [Algebra k M] [Algebra k F] [Algebra k FM] [Algebra M FM] [Algebra F FM]
    [IsScalarTower k M FM] [IsScalarTower k F FM] {p : ℕ} [Fact p.Prime] [CharP k p]
    [FiniteDimensional k M] (hF : IsFunctionField k F) (hex : IsIntegrallyClosedIn k F)
    (hFM : constantCompositum F M FM = ⊤) (hexM : IsIntegrallyClosedIn M FM) :
    (p - 1) ∣ 2 * (genus k F - genus M FM) := by
  let S : IntermediateField k M := separableClosure k M
  let FS := constantCompositum F S FM
  let := constantCompositumAlgebra F S FM
  have := isScalarTower_constantCompositum F S FM
  have := isScalarTower_base_constantCompositum k F S FM
  have hFS : constantCompositum F S FS = ⊤ := (constantCompositum_eq_top_iff F S FM FS).2 rfl
  have hFFS : IsFunctionField S FS := hF.of_constantCompositum_eq_top hFS
  have hexS : IsIntegrallyClosedIn S FS := IsIntegrallyClosedIn.of_constantCompositum_eq_top hex hFS
  have hgS : genus S FS = genus k F := genus_eq_genus_of_constantCompositum_eq_top hF hex hFS
  have hFSM : constantCompositum FS M FM = ⊤ := constantCompositum_eq_top_of_eq_top F M FM FS hFM
  have : CharP S p := charP_of_injective_algebraMap (algebraMap k S).injective p
  have : IsPurelyInseparable S M := separableClosure.isPurelyInseparable k M
  rw [← hgS]
  exact sub_one_dvd_two_mul_genus_sub_genus_of_isPurelyInseparable_of_finite p (finrank S M)
    S M FS FM rfl hFFS hexS hFSM hexM

variable {k : Type u} {k' : Type u'} {F : Type v} {F' : Type v'}
variable [Field k] [Field k'] [Field F] [Field F']
variable [Algebra k k'] [Algebra k F] [Algebra k F'] [Algebra k' F'] [Algebra F F']
variable [IsScalarTower k k' F'] [IsScalarTower k F F']

/-- **Tate's genus-change theorem** (exact constants): for any algebraic constant field extension
`F' = F · k'` of a function field `F / k` in prime characteristic `p`, finite or infinite, if `k`
is exact in `F` and `k'` is exact in `F'`, then `p - 1` divides `2 (g(F / k) - g(F' / k'))`. -/
theorem sub_one_dvd_two_mul_genus_sub_genus_of_isIntegrallyClosedIn {p : ℕ} [Fact p.Prime]
    [CharP k p] [Algebra.IsAlgebraic k k'] (hF : IsFunctionField k F)
    (hex : IsIntegrallyClosedIn k F) (h : constantCompositum F k' F' = ⊤)
    (hex' : IsIntegrallyClosedIn k' F') :
    (p - 1) ∣ 2 * (genus k F - genus k' F') := by
  obtain ⟨L, _, hexL, hgL⟩ := exists_finiteDimensional_isIntegrallyClosedIn_genus_eq hF h hex'
  let FL := constantCompositum F L F'
  let := constantCompositumAlgebra F L F'
  have := isScalarTower_constantCompositum F L F'
  have := isScalarTower_base_constantCompositum k F L F'
  have hFL : constantCompositum F L FL = ⊤ := (constantCompositum_eq_top_iff F L F' FL).2 rfl
  rw [← hgL]
  exact sub_one_dvd_two_mul_genus_sub_genus_of_finite_of_isIntegrallyClosedIn hF hex hFL hexL

/-- **Tate's genus-change theorem** (allowing constant growth): for any algebraic constant field
extension `F' = F · k'` of a function field `F / k` in prime characteristic `p` with `k` exact in
`F`, and any algebraic enlargement `k'' / k'` inside `F'` that is exact in `F'`, `p - 1` divides
`2 (g(F / k) - g(F' / k''))`. -/
theorem sub_one_dvd_two_mul_genus_sub_genus_of_constantCompositum_eq_top {p : ℕ} [Fact p.Prime]
    [CharP k p] [Algebra.IsAlgebraic k k'] (hF : IsFunctionField k F)
    (hex : IsIntegrallyClosedIn k F) (h : constantCompositum F k' F' = ⊤)
    {k'' : Type*} [Field k''] [Algebra k' k''] [Algebra k'' F'] [IsScalarTower k' k'' F']
    [Algebra.IsAlgebraic k' k''] (hex'' : IsIntegrallyClosedIn k'' F') :
    (p - 1) ∣ 2 * (genus k F - genus k'' F') := by
  let _ : Algebra k k'' := RingHom.toAlgebra ((algebraMap k' k'').comp (algebraMap k k'))
  have : IsScalarTower k k' k'' := .of_algebraMap_eq fun _ ↦ rfl
  have : IsScalarTower k k'' F' := .of_algebraMap_eq fun c ↦ by
    rw [RingHom.algebraMap_toAlgebra, RingHom.comp_apply,
      ← IsScalarTower.algebraMap_apply k' k'' F', ← IsScalarTower.algebraMap_apply k k' F']
  have : Algebra.IsAlgebraic k k'' := Algebra.IsAlgebraic.trans k k' k''
  exact sub_one_dvd_two_mul_genus_sub_genus_of_isIntegrallyClosedIn hF hex
    (constantCompositum_eq_top_of_isScalarTower h) hex''

/-- **Tate's genus-change theorem for `algebraicClosure k' F'`**: specialization of
`TauCeti.sub_one_dvd_two_mul_genus_sub_genus_of_constantCompositum_eq_top` to
`k'' = algebraicClosure k' F'` for an algebraic constant field extension `F' = F · k'` of a function
field `F / k` in prime characteristic `p` with `k` exact in `F`, requiring no exactness hypothesis
on `k'` in `F'`. -/
theorem sub_one_dvd_two_mul_genus_sub_genus_algebraicClosure_of_constantCompositum_eq_top {p : ℕ}
    [Fact p.Prime] [CharP k p] [Algebra.IsAlgebraic k k'] (hF : IsFunctionField k F)
    (hex : IsIntegrallyClosedIn k F) (h : constantCompositum F k' F' = ⊤) :
    (p - 1) ∣ 2 * (genus k F - genus (algebraicClosure k' F') F') :=
  sub_one_dvd_two_mul_genus_sub_genus_of_constantCompositum_eq_top hF hex h
    (isIntegrallyClosedIn_algebraicClosure (k := k') (F := F'))

/-- **Odd-characteristic Tate divisibility**: for a function field `F / k` in odd prime
characteristic `p` with `k` exact in `F`, `(p - 1) / 2` divides the genus drop
`g(F / k) - g(F' / k'')` across any algebraic constant field extension `F' = F · k'` and any
algebraic extension `k'' / k'` inside `F'` that is exact in `F'`. -/
theorem sub_one_div_two_dvd_genus_sub_genus_of_constantCompositum_eq_top {p : ℕ} [Fact p.Prime]
    [CharP k p] (hp2 : p ≠ 2) [Algebra.IsAlgebraic k k'] (hF : IsFunctionField k F)
    (hex : IsIntegrallyClosedIn k F) (h : constantCompositum F k' F' = ⊤)
    {k'' : Type*} [Field k''] [Algebra k' k''] [Algebra k'' F'] [IsScalarTower k' k'' F']
    [Algebra.IsAlgebraic k' k''] (hex'' : IsIntegrallyClosedIn k'' F') :
    ((p - 1) / 2) ∣ genus k F - genus k'' F' := by
  have hp : p.Prime := Fact.out
  have h2 : 2 * ((p - 1) / 2) = p - 1 :=
    Nat.mul_div_cancel' ((hp.odd_of_ne_two hp2).tsub_odd odd_one).two_dvd
  refine (Nat.mul_dvd_mul_iff_left two_pos).1 ?_
  rw [h2]
  exact sub_one_dvd_two_mul_genus_sub_genus_of_constantCompositum_eq_top hF hex h hex''

/-- **Genus conservation in small genus**: for a function field `F / k` in prime characteristic `p`
with `k` exact in `F`, if `2 g(F / k) < p - 1`, then `g(F' / k'') = g(F / k)` for every algebraic
constant field extension `F' = F · k'` and every algebraic extension `k'' / k'` inside `F'` that is
exact in `F'`. -/
theorem genus_eq_genus_of_two_mul_genus_lt_sub_one {p : ℕ} [Fact p.Prime] [CharP k p]
    [Algebra.IsAlgebraic k k'] (hF : IsFunctionField k F) (hex : IsIntegrallyClosedIn k F)
    (h : constantCompositum F k' F' = ⊤) (hlt : 2 * genus k F < p - 1)
    {k'' : Type*} [Field k''] [Algebra k' k''] [Algebra k'' F'] [IsScalarTower k' k'' F']
    [Algebra.IsAlgebraic k' k''] (hex'' : IsIntegrallyClosedIn k'' F') :
    genus k'' F' = genus k F := by
  let _ : Algebra k k'' := RingHom.toAlgebra ((algebraMap k' k'').comp (algebraMap k k'))
  have : IsScalarTower k k' k'' := .of_algebraMap_eq fun _ ↦ rfl
  have : IsScalarTower k k'' F' := .of_algebraMap_eq fun c ↦ by
    rw [RingHom.algebraMap_toAlgebra, RingHom.comp_apply,
      ← IsScalarTower.algebraMap_apply k' k'' F', ← IsScalarTower.algebraMap_apply k k' F']
  have : Algebra.IsAlgebraic k k'' := Algebra.IsAlgebraic.trans k k' k''
  have hgle : genus k'' F' ≤ genus k F :=
    genus_le_genus_of_constantCompositum_eq_top hF (constantCompositum_eq_top_of_isScalarTower h)
  have hdvd := sub_one_dvd_two_mul_genus_sub_genus_of_constantCompositum_eq_top hF hex h hex''
  have hzero : 2 * (genus k F - genus k'' F') = 0 := Nat.eq_zero_of_dvd_of_lt hdvd (by omega)
  omega

/-- **Genus conservation in odd characteristic**: for a function field `F / k` in odd prime
characteristic `p` with `k` exact in `F`, if `g(F / k) < (p - 1) / 2`, then
`g(F' / k'') = g(F / k)` for every algebraic constant field extension `F' = F · k'` and every
algebraic extension `k'' / k'` inside `F'` that is exact in `F'`. -/
theorem genus_eq_genus_of_genus_lt_sub_one_div_two {p : ℕ} [Fact p.Prime] [CharP k p] (hp2 : p ≠ 2)
    [Algebra.IsAlgebraic k k'] (hF : IsFunctionField k F) (hex : IsIntegrallyClosedIn k F)
    (h : constantCompositum F k' F' = ⊤) (hlt : genus k F < (p - 1) / 2)
    {k'' : Type*} [Field k''] [Algebra k' k''] [Algebra k'' F'] [IsScalarTower k' k'' F']
    [Algebra.IsAlgebraic k' k''] (hex'' : IsIntegrallyClosedIn k'' F') :
    genus k'' F' = genus k F := by
  have hp : p.Prime := Fact.out
  have h2 : 2 * ((p - 1) / 2) = p - 1 :=
    Nat.mul_div_cancel' ((hp.odd_of_ne_two hp2).tsub_odd odd_one).two_dvd
  exact genus_eq_genus_of_two_mul_genus_lt_sub_one hF hex h (by omega) hex''

/-- **Exactness of constants in small positive genus**: for a function field `F / k` in prime
characteristic `p` with exact constant field `k`, if `1 ≤ g(F / k)` and `2 g(F / k) < p - 1`, then
for every algebraic constant field extension `F' = F · k'` (finite or infinite), `k'` remains the
exact constant field of `F'`. -/
theorem isIntegrallyClosedIn_of_one_le_genus_of_two_mul_genus_lt_sub_one {p : ℕ} [Fact p.Prime]
    [CharP k p] [Algebra.IsAlgebraic k k'] (hF : IsFunctionField k F)
    (hex : IsIntegrallyClosedIn k F) (h : constantCompositum F k' F' = ⊤)
    (hg1 : 1 ≤ genus k F) (hlt : 2 * genus k F < p - 1) :
    IsIntegrallyClosedIn k' F' :=
  isIntegrallyClosedIn_of_one_le_genus_of_genus_eq hF hex h hg1
    (isIntegrallyClosedIn_algebraicClosure (k := k') (F := F'))
    (genus_eq_genus_of_two_mul_genus_lt_sub_one hF hex h hlt
      (isIntegrallyClosedIn_algebraicClosure (k := k') (F := F')))

end Tate

end TauCeti
