/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.ConstantExtension.Singularity.Basic
import TauCeti.FieldTheory.FunctionField.ConstantExtension.Algebraic
import TauCeti.FieldTheory.FunctionField.GeometricDegree
import TauCeti.FieldTheory.FunctionField.Place.Extension.PurelyInseparable
import TauCeti.FieldTheory.FunctionField.Place.OrderOfVanishing
import TauCeti.FieldTheory.IntermediateField.Adjoin.PrimitiveElement
import TauCeti.FieldTheory.PurelyInseparable.Basic
import TauCeti.FieldTheory.PurelyInseparable.Exponent
import TauCeti.LinearAlgebra.Matrix.Nonsingular.Basic
import TauCeti.RingTheory.Length.Determinant
import TauCeti.RingTheory.PowerBasis.Determinant

/-!
# Local Tate–Schröer formula for the singularity degree

For a purely inseparable constant field extension `F' = F · k'` of prime degree `p` over an
algebraic function field `F / k` with exact constant field `k`, each place `P` of `F / k` has a
unique place `P'` of `F' / k'` above it. By Nakayama's criterion
(`TauCeti.Place.exists_powerBasis_integers_of_finrank_eq_prime`), `𝒪_{P'}` admits an `𝒪_P`-power
basis `1, β, …, β ^ (p - 1)` with `β ^ p ∈ 𝒪_P`.

Writing a primitive element `α` of `k' / k` as `f(β)` for a polynomial `f ∈ 𝒪_P[X]`, the
transition matrix `A` from `1, β, …, β ^ (p - 1)` to `1, α, …, α ^ (p - 1)` reduces `f(X) ^ i`
modulo `X ^ p - β ^ p`. Over `𝒪_{P'}`, this modulus factors as `(X - β) ^ p`, so
`PowerBasis.det_toMatrix_aeval_pow` evaluates `det A` as `f'(β) ^ (p (p - 1) / 2)`. Comparing
`𝒪_P`-lengths and `k`-dimensions yields the local Tate–Schröer formula

`2 δ_P = (p - 1) · ord_{P'}(f'(β)) · deg P'`,

and hence the local divisibility `(p - 1) ∣ 2 δ_P` (and `(p - 1) / 2 ∣ δ_P` for odd `p`).

## Main results

* `TauCeti.Place.two_mul_singularityDegree_restrict_eq_of_finrank_eq_prime` and
  `TauCeti.Place.exists_two_mul_singularityDegree_restrict_eq_of_finrank_eq_prime`: the local
  Tate–Schröer formula `2 δ_P = (p - 1) · ord_{P'}(f'(pb.gen)) · deg P'`.
* `TauCeti.Place.sub_one_dvd_two_mul_singularityDegree_of_finrank_eq_prime` and
  `TauCeti.Place.sub_one_div_two_dvd_singularityDegree_of_finrank_eq_prime`: local divisibility
  `(p - 1) ∣ 2 δ_P` (and `(p - 1) / 2 ∣ δ_P` when `p ≠ 2`) for a purely inseparable constant
  extension of prime degree `p`.

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

end TauCeti
