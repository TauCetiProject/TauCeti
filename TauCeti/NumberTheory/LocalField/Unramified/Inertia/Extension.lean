/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.Galois.AbsoluteGaloisGroup.FiniteExtension
public import TauCeti.NumberTheory.LocalField.InertiaDegree
public import TauCeti.NumberTheory.LocalField.Unramified.Inertia.Basic
import TauCeti.NumberTheory.LocalField.Teichmuller

/-!
# Inertia and Frobenius along a finite extension of local fields

Let `L/K` be a finite extension of nonarchimedean local fields with residue degree `f = f(L/K)`,
embedded in a separable closure of `K` by `ι`, and let
`absoluteGaloisGroupExtend K L ι : G_L →* G_K` be the resulting embedding of absolute Galois groups.
If `q` is the cardinality of the residue field of `K`, that of `L` is `q^f`, so the generators of
the maximal unramified extensions, the roots of the polynomials `X^{q^g} − X` and `X^{q^{fg}} − X`,
correspond under the identification of separable closures. Consequently an element `τ ∈ G_L` acts
on `L^{ur}` as the `n`-th power of the arithmetic Frobenius of `L` exactly when its image acts on
`K^{ur}` as the `f n`-th power of the arithmetic Frobenius of `K`. In particular:

* the inertia subgroup of `L` is the preimage of that of `K`;
* an arithmetic Frobenius lift of `L` acts on `K^{ur}` as the `f`-th power of Frobenius;
* if the image of `τ` acts on `K^{ur}` as an integral power `m` of Frobenius, then `f ∣ m`: the
  element fixes `L`, and hence its Teichmüller representatives, whose residues generate the
  degree-`f` extension of the residue field of `K`.

These are the inputs of the functoriality of the local Weil group under finite extensions.

## Main results

* `TauCeti.restrictMaximalUnramifiedHom_absoluteGaloisGroupExtend_eq_zpow_iff`: the image of
  `τ ∈ G_L` acts on `K^{ur}` as `Frob_K ^ (f n)` exactly when `τ` acts on `L^{ur}` as
  `Frob_L ^ n`, for every integer `n`.
* `TauCeti.absoluteGaloisGroupExtend_mem_inertiaSubgroup_iff`: `I_L` is the preimage of `I_K`.
* `TauCeti.IsArithFrobeniusLift.restrictMaximalUnramifiedHom_absoluteGaloisGroupExtend`: an
  arithmetic Frobenius lift of `L` acts on `K^{ur}` as `Frob_K ^ f`.
* `TauCeti.inertiaDegree_dvd_of_restrictMaximalUnramifiedHom_absoluteGaloisGroupExtend_eq_zpow`:
  an element of `G_L` acting on `K^{ur}` as `Frob_K ^ m` has `f ∣ m`.

## References

* J.-P. Serre, *Local Fields*, Chapter III, §5.
* J. Neukirch, *Algebraic Number Theory*, Chapter II, §9.
-/

public section

noncomputable section

open ValuativeRel IntermediateField

namespace TauCeti

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-- The roots of the polynomials `X^{q^g} − X`, `g ≠ 0`, are separable over `K`: they generate the
maximal unramified extension, which is Galois over `K`. -/
private theorem mem_separableClosure_of_pow_natCard_pow_eq_self {x : AlgebraicClosure K} {g : ℕ}
    (hg : g ≠ 0) (hx : x ^ Nat.card 𝓀[K] ^ g = x) :
    x ∈ separableClosure K (AlgebraicClosure K) :=
  le_separableClosure K _ (maximalUnramifiedExtension K (AlgebraicClosure K))
    ((maximalUnramifiedExtension_eq_adjoin K _).ge (subset_adjoin _ _ ⟨g, hg, hx⟩))

variable {L : Type*} [Field L] [ValuativeRel L] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L] [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]
  (ι : L →ₐ[K] SeparableClosure K)

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] [ValuativeRel L]
  [TopologicalSpace L] [IsNonarchimedeanLocalField L] [ValuativeExtension K L] in
/-- **Transport of the action on roots along `absoluteGaloisGroupExtend`.** Let `M, N : ℕ` be
such that the roots of `X^M − X` are separable over both `K` and `L`. Then the image of `τ ∈ G_L`
raises every root of `X^M − X` in `K^{alg}` to the `N`-th power exactly when `τ` raises every
root of `X^M − X` in `L^{alg}` to the `N`-th power, since the separable closures of `K` and `L` are
identified compatibly with the two Galois actions. -/
private theorem forall_absoluteGaloisGroupExtend_apply_iff (τ : Field.absoluteGaloisGroup L)
    {M N : ℕ}
    (hK : ∀ x : AlgebraicClosure K, x ^ M = x → x ∈ separableClosure K (AlgebraicClosure K))
    (hL : ∀ z : AlgebraicClosure L, z ^ M = z → z ∈ separableClosure L (AlgebraicClosure L)) :
    (∀ x : AlgebraicClosure K, x ^ M = x →
        DFunLike.coe (F := Gal(AlgebraicClosure K/K)) (absoluteGaloisGroupExtend K L ι τ) x =
          x ^ N) ↔
      ∀ z : AlgebraicClosure L, z ^ M = z →
        DFunLike.coe (F := Gal(AlgebraicClosure L/L)) τ z = z ^ N := by
  set e := separableClosureRingEquiv K L ι
  -- On `Lˢ`, the image of `τ` acts through `e` as `τ` does.
  have key (z : SeparableClosure L) :
      DFunLike.coe (F := Gal(AlgebraicClosure K/K)) (absoluteGaloisGroupExtend K L ι τ)
          (e z : AlgebraicClosure K) =
        (e (absoluteGaloisGroupRestrictEquiv L τ z) : AlgebraicClosure K) :=
    (coe_absoluteGaloisGroupRestrictEquiv_apply K _ (e z)).symm.trans
      (congrArg Subtype.val (absoluteGaloisGroupExtend_apply_separableClosureRingEquiv K L ι τ z))
  have hfix (z : SeparableClosure L) : (e z : AlgebraicClosure K) ^ M = e z ↔ z ^ M = z := by
    rw [← SubmonoidClass.coe_pow, ← map_pow, Subtype.coe_inj, e.injective.eq_iff]
  have hact (z : SeparableClosure L) :
      DFunLike.coe (F := Gal(AlgebraicClosure K/K)) (absoluteGaloisGroupExtend K L ι τ)
          (e z : AlgebraicClosure K) = (e z : AlgebraicClosure K) ^ N ↔
        DFunLike.coe (F := Gal(AlgebraicClosure L/L)) τ (z : AlgebraicClosure L) =
          (z : AlgebraicClosure L) ^ N := by
    rw [key, ← SubmonoidClass.coe_pow, ← map_pow, Subtype.coe_inj, e.injective.eq_iff,
      ← Subtype.coe_inj, coe_absoluteGaloisGroupRestrictEquiv_apply L τ z, SubmonoidClass.coe_pow]
  refine ⟨fun h z hz ↦ ?_, fun h x hx ↦ ?_⟩
  · set zs : SeparableClosure L := ⟨z, hL z hz⟩
    exact (hact zs).1 (h _ ((hfix zs).2 (Subtype.ext (by simpa [zs] using hz))))
  · set zs : SeparableClosure L := e.symm ⟨x, hK x hx⟩
    have hzs : (e zs : AlgebraicClosure K) = x := by simp [zs]
    have hzM : zs ^ M = zs := (hfix zs).1 (by rw [hzs, hx])
    rw [← hzs]
    exact (hact zs).2 (h _ (by rw [← SubmonoidClass.coe_pow, hzM]))

/-- Transport of the action on the generators of the maximal unramified extensions: the image of
`τ ∈ G_L` raises the roots of the polynomials `X^{q^g} − X` over `K` to the `q^{f n}`-th power
exactly when `τ` raises the roots of the polynomials `X^{(q^f)^g} − X` over `L` to the `(q^f)^n`-th
power. -/
private theorem forall_absoluteGaloisGroupExtend_apply_pow_iff (τ : Field.absoluteGaloisGroup L)
    (n : ℕ) :
    (∀ (x : AlgebraicClosure K) (g : ℕ), g ≠ 0 → x ^ Nat.card 𝓀[K] ^ g = x →
        DFunLike.coe (F := Gal(AlgebraicClosure K/K)) (absoluteGaloisGroupExtend K L ι τ) x =
          x ^ Nat.card 𝓀[K] ^ (inertiaDegree K L * n)) ↔
      ∀ (z : AlgebraicClosure L) (g : ℕ), g ≠ 0 → z ^ Nat.card 𝓀[L] ^ g = z →
        DFunLike.coe (F := Gal(AlgebraicClosure L/L)) τ z = z ^ Nat.card 𝓀[L] ^ n := by
  have hf : inertiaDegree K L ≠ 0 := inertiaDegree_pos.ne'
  -- A root of `X^{q^g} − X` is a root of `X^{(q^f)^g} − X = X^{(q^g)^f} − X`.
  have hroot {z : AlgebraicClosure L} {g : ℕ} (hz : z ^ Nat.card 𝓀[K] ^ g = z) :
      z ^ Nat.card 𝓀[L] ^ g = z := by
    rw [natCard_residueField K L, ← pow_mul, mul_comm, pow_mul]
    have h := Function.IsFixedPt.iterate (f := (· ^ Nat.card 𝓀[K] ^ g)) hz (inertiaDegree K L)
    rwa [pow_iterate] at h
  have hexp : Nat.card 𝓀[K] ^ (inertiaDegree K L * n) = Nat.card 𝓀[L] ^ n := by
    rw [natCard_residueField K L, pow_mul]
  simp_rw [hexp]
  refine ⟨fun h z g hg hz ↦ ?_, fun h x g hg hx ↦ ?_⟩
  · -- The roots of `X^{(q^f)^g} − X` are those of `X^{q^{f g}} − X`.
    rw [natCard_residueField K L, ← pow_mul] at hz ⊢
    refine (forall_absoluteGaloisGroupExtend_apply_iff ι τ
      (fun x hx ↦ mem_separableClosure_of_pow_natCard_pow_eq_self (mul_ne_zero hf hg) hx)
      (fun z hz ↦ mem_separableClosure_of_pow_natCard_pow_eq_self hg
        (by rwa [natCard_residueField K L, ← pow_mul]))).1
      (fun x hx ↦ ?_) z hz
    rw [hexp]
    exact h x _ (mul_ne_zero hf hg) hx
  · exact (forall_absoluteGaloisGroupExtend_apply_iff ι τ
      (fun x hx ↦ mem_separableClosure_of_pow_natCard_pow_eq_self hg hx)
      (fun z hz ↦ mem_separableClosure_of_pow_natCard_pow_eq_self hg (hroot hz))).2
      (fun z hz ↦ h z g hg (hroot hz)) x hx

/-- **Frobenius along a finite extension.** For `n : ℕ`, the image of `τ ∈ G_L` in `G_K` acts on
`K^{ur}` as the `f n`-th power of the arithmetic Frobenius of `K`, where `f = f(L/K)`, exactly when
`τ` acts on `L^{ur}` as the `n`-th power of the arithmetic Frobenius of `L`. -/
theorem restrictMaximalUnramifiedHom_absoluteGaloisGroupExtend_eq_pow_iff
    (τ : Field.absoluteGaloisGroup L) (n : ℕ) :
    restrictMaximalUnramifiedHom K (absoluteGaloisGroupExtend K L ι τ) =
        maximalUnramifiedFrobenius K (AlgebraicClosure K) ^ (inertiaDegree K L * n) ↔
      restrictMaximalUnramifiedHom L τ = maximalUnramifiedFrobenius L (AlgebraicClosure L) ^ n := by
  rw [restrictMaximalUnramifiedHom_eq_frobenius_pow_iff,
    restrictMaximalUnramifiedHom_eq_frobenius_pow_iff]
  exact forall_absoluteGaloisGroupExtend_apply_pow_iff ι τ n

/-- **Frobenius along a finite extension, integral powers.** For `n : ℤ`, the image of
`τ ∈ G_L` in `G_K` acts on `K^{ur}` as the `f n`-th power of the arithmetic Frobenius of `K`, where
`f = f(L/K)`, exactly when `τ` acts on `L^{ur}` as the `n`-th power of the arithmetic Frobenius of
`L`. -/
theorem restrictMaximalUnramifiedHom_absoluteGaloisGroupExtend_eq_zpow_iff
    (τ : Field.absoluteGaloisGroup L) (n : ℤ) :
    restrictMaximalUnramifiedHom K (absoluteGaloisGroupExtend K L ι τ) =
        maximalUnramifiedFrobenius K (AlgebraicClosure K) ^ ((inertiaDegree K L : ℤ) * n) ↔
      restrictMaximalUnramifiedHom L τ = maximalUnramifiedFrobenius L (AlgebraicClosure L) ^ n := by
  obtain ⟨n, rfl | rfl⟩ := n.eq_nat_or_neg
  · exact_mod_cast restrictMaximalUnramifiedHom_absoluteGaloisGroupExtend_eq_pow_iff ι τ n
  · -- Apply the natural-number case to `τ⁻¹`.
    have h := restrictMaximalUnramifiedHom_absoluteGaloisGroupExtend_eq_pow_iff ι τ⁻¹ n
    rw [map_inv, map_inv, map_inv, inv_eq_iff_eq_inv, inv_eq_iff_eq_inv] at h
    rw [mul_neg, zpow_neg, zpow_neg, ← Nat.cast_mul, zpow_natCast, zpow_natCast]
    exact h

/-- **Inertia along a finite extension.** An element of `G_L` lies in the inertia subgroup of `L`
exactly when its image in `G_K` lies in the inertia subgroup of `K`: `I_L` is the preimage of
`I_K`. -/
theorem absoluteGaloisGroupExtend_mem_inertiaSubgroup_iff {τ : Field.absoluteGaloisGroup L} :
    absoluteGaloisGroupExtend K L ι τ ∈ inertiaSubgroup K ↔ τ ∈ inertiaSubgroup L := by
  simpa [← ker_restrictMaximalUnramifiedHom] using
    restrictMaximalUnramifiedHom_absoluteGaloisGroupExtend_eq_pow_iff ι τ 0

/-- **Frobenius lifts along a finite extension.** An arithmetic Frobenius lift of `L` acts on
`K^{ur}` as the `f`-th power of the arithmetic Frobenius of `K`, where `f = f(L/K)`. -/
theorem IsArithFrobeniusLift.restrictMaximalUnramifiedHom_absoluteGaloisGroupExtend
    {τ : Field.absoluteGaloisGroup L} (hτ : IsArithFrobeniusLift L τ) :
    restrictMaximalUnramifiedHom K (absoluteGaloisGroupExtend K L ι τ) =
      maximalUnramifiedFrobenius K (AlgebraicClosure K) ^ inertiaDegree K L := by
  simpa using (restrictMaximalUnramifiedHom_absoluteGaloisGroupExtend_eq_pow_iff ι τ 1).2
    (by simpa using hτ)

/-- If the image of `τ ∈ G_L` acts on `K^{ur}` as the `m`-th power of Frobenius, for `m : ℕ`, then
`τ` raises every element of the residue field of `L` to the `q^m`-th power: it fixes the
Teichmüller representatives, which are roots of `X^{q^f} − X`. -/
private theorem pow_natCard_pow_eq_self_of_restrictMaximalUnramifiedHom_eq_pow
    {τ : Field.absoluteGaloisGroup L} {m : ℕ}
    (h : restrictMaximalUnramifiedHom K (absoluteGaloisGroupExtend K L ι τ) =
      maximalUnramifiedFrobenius K (AlgebraicClosure K) ^ m) (a : 𝓀[L]) :
    a ^ Nat.card 𝓀[K] ^ m = a := by
  have hf : inertiaDegree K L ≠ 0 := inertiaDegree_pos.ne'
  -- `τ` raises the roots of `X^{q^f} − X` in `L^{alg}` to the `q^m`-th power.
  have hτ := (forall_absoluteGaloisGroupExtend_apply_iff ι τ
    (M := Nat.card 𝓀[K] ^ inertiaDegree K L)
    (fun x hx ↦ mem_separableClosure_of_pow_natCard_pow_eq_self hf hx)
    (fun z hz ↦ mem_separableClosure_of_pow_natCard_pow_eq_self one_ne_zero
      (by rwa [pow_one, natCard_residueField K L]))).1
    (fun x hx ↦ restrictMaximalUnramifiedHom_eq_frobenius_pow_iff.1 h x _ hf hx)
  -- The Teichmüller representative `ω` of `a` is such a root, and `τ` fixes it.
  set ω : L := ((teichmullerLift L a : 𝒪[L]) : L)
  have hω : ω ^ Nat.card 𝓀[K] ^ inertiaDegree K L = ω := by
    rw [← natCard_residueField K L]
    exact congrArg Subtype.val (teichmullerLift_pow_natCard L a)
  have h' := hτ (algebraMap L (AlgebraicClosure L) ω) (by rw [← map_pow, hω])
  have hc : DFunLike.coe (F := Gal(AlgebraicClosure L/L)) τ (algebraMap L (AlgebraicClosure L) ω) =
      algebraMap L (AlgebraicClosure L) ω :=
    AlgEquiv.commutes τ ω
  rw [hc, ← map_pow] at h'
  have hω' : teichmullerLift L a ^ Nat.card 𝓀[K] ^ m = teichmullerLift L a :=
    Subtype.ext ((FaithfulSMul.algebraMap_injective L _ h').symm.trans (by simp [ω]))
  simpa using congrArg (IsLocalRing.residue 𝒪[L]) hω'

/-- The natural-number case of
`inertiaDegree_dvd_of_restrictMaximalUnramifiedHom_absoluteGaloisGroupExtend_eq_zpow`. -/
private theorem inertiaDegree_dvd_of_restrictMaximalUnramifiedHom_absoluteGaloisGroupExtend_eq_pow
    {τ : Field.absoluteGaloisGroup L} {m : ℕ}
    (h : restrictMaximalUnramifiedHom K (absoluteGaloisGroupExtend K L ι τ) =
      maximalUnramifiedFrobenius K (AlgebraicClosure K) ^ m) :
    inertiaDegree K L ∣ m := by
  let _ := Fintype.ofFinite 𝓀[K]
  let _ := Fintype.ofFinite 𝓀[L]
  -- The `m`-th power of the Frobenius of `𝓀[L] / 𝓀[K]` is trivial, and its order is `f`.
  rw [inertiaDegree_def, ← FiniteField.orderOf_frobeniusAlgEquivOfAlgebraic 𝓀[K] 𝓀[L]]
  refine orderOf_dvd_of_pow_eq_one (AlgEquiv.ext fun a ↦ ?_)
  rw [AlgEquiv.coe_pow, FiniteField.coe_frobeniusAlgEquivOfAlgebraic_iterate, AlgEquiv.one_apply,
    ← Nat.card_eq_fintype_card]
  exact pow_natCard_pow_eq_self_of_restrictMaximalUnramifiedHom_eq_pow ι h a

/-- **Divisibility by the residue degree.** If the image of `τ ∈ G_L` in `G_K` acts on `K^{ur}` as
the `m`-th power of the arithmetic Frobenius of `K`, then the residue degree `f(L/K)` divides `m`:
the `q^m`-th power map fixes the residue field of `L`, of degree `f(L/K)` over that of `K`. -/
theorem inertiaDegree_dvd_of_restrictMaximalUnramifiedHom_absoluteGaloisGroupExtend_eq_zpow
    {τ : Field.absoluteGaloisGroup L} {m : ℤ}
    (h : restrictMaximalUnramifiedHom K (absoluteGaloisGroupExtend K L ι τ) =
      maximalUnramifiedFrobenius K (AlgebraicClosure K) ^ m) :
    (inertiaDegree K L : ℤ) ∣ m := by
  obtain ⟨k, rfl | rfl⟩ := m.eq_nat_or_neg
  · exact Int.natCast_dvd_natCast.2
      (inertiaDegree_dvd_of_restrictMaximalUnramifiedHom_absoluteGaloisGroupExtend_eq_pow ι
        (by exact_mod_cast h))
  · -- Apply the natural-number case to `τ⁻¹`.
    refine Int.dvd_neg.2 (Int.natCast_dvd_natCast.2
      (inertiaDegree_dvd_of_restrictMaximalUnramifiedHom_absoluteGaloisGroupExtend_eq_pow ι
        (τ := τ⁻¹) ?_))
    rw [map_inv, map_inv, h, zpow_neg, inv_inv, zpow_natCast]

end TauCeti
