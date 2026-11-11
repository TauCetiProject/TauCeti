/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.MultiplicativeGroup.WeilRestriction.Basic
public import TauCeti.Algebra.AlgebraicGroup.Connected.AlgebraicallyClosed
import Mathlib.RingTheory.HopfAlgebra.TensorProduct
import Mathlib.RingTheory.Localization.Away.Basic
import TauCeti.Algebra.AlgebraicGroup.BaseChange.Basic
import TauCeti.Algebra.Polynomial.Homogenize
import TauCeti.FieldTheory.Minpoly
import TauCeti.RingTheory.Spectrum.Prime.Topology

/-!
# Connectedness of the Weil restriction of the multiplicative group

Let `B` be a finite-dimensional commutative algebra over a field `k`. The Weil restriction
`Res_{B/k} 𝔾ₘ`, with coordinate Hopf algebra `WeilRestriction k B B[T;T⁻¹]`, is geometrically
connected. This applies in particular to `B = K` for a finite field extension `K / k`. Together
with smoothness and commutativity (`WeilRestriction.instSmooth`, `WeilRestriction.instIsCocomm`),
`Res_{K/k} 𝔾ₘ` is then a smooth connected commutative group. For `K / k` purely inseparable and
nontrivial it is the standard example of a pseudo-reductive group which is not reductive; neither
of these two properties is proved here.

## Main declarations

* `TauCeti.Algebra.WeilRestriction.geometricallyConnectedCommHopfAlgProperty_multiplicativeGroup`:
  the Weil restriction of `𝔾ₘ` along a finite-dimensional algebra over a field is geometrically
  connected.

## Implementation notes

Geometrically, `Res_{B/k} 𝔾ₘ` is the open subscheme of the affine space of `B` on which the norm
does not vanish, so it is irreducible. The proof here avoids norms and works with idempotents
and points. Over an algebraically closed extension `Ω` of `k`, an `Ω`-point is a unit `u` of
`B ⊗[k] Ω`. If `p` is a nonzero polynomial over `Ω` annihilating `u` with `p(0) ≠ 0`, and
`n = deg p`, put

```text
ρ(s) = ∑ᵢ pᵢ sⁿ⁻ⁱ (s - 1)ⁱ,
```

the binary homogenization of `p` of degree `n` evaluated at `(s - 1, s)`. Then `1 - s + s u`
divides `ρ(s)` (`Polynomial.sub_mul_dvd_eval_homogenize`), while `ρ(0) = ± pₙ` and `ρ(1) = p₀`
are nonzero. Hence `s ↦ 1 - s + s u` is a point of `Res_{B/k} 𝔾ₘ` with values in the domain
`Ω[s][1/ρ]`, joining the identity at `s = 0` to `u` at `s = 1`. An idempotent takes the value `0`
or `1` on such a path, so every idempotent of the geometric coordinate ring has the same value at
every `Ω`-point. By the Nullstellensatz it is `0` or `1`.

## References

* B. Conrad, O. Gabber, G. Prasad, *Pseudo-reductive Groups*, 2nd ed. (2015), §1.1 and §A.5.
* J. S. Milne, *Algebraic Groups* (2017), §2.i.
-/

public section

open Polynomial WithConv
open scoped LaurentPolynomial TensorProduct

namespace TauCeti.Algebra.WeilRestriction

universe u

section PathPolynomial

variable {K : Type*} [CommRing K]

/-- The polynomial `ρ(s) = F(s - 1, s) = ∑ᵢ pᵢ sⁿ⁻ⁱ (s - 1)ⁱ`, where `F` is the binary
homogenization of `p` of degree `n = natDegree p`. When `p` annihilates `u`, it is divisible by
`1 - s + s u`. -/
private noncomputable def pathPolynomial (p : K[X]) : K[X] :=
  MvPolynomial.aeval ![X - 1, X] (p.homogenize p.natDegree)

private theorem eval₂_pathPolynomial {S : Type*} [CommRing S] (κ : K →+* S) (p : K[X]) (s : S) :
    (pathPolynomial p).eval₂ κ s =
      MvPolynomial.eval ![s - 1, s] ((p.map κ).homogenize p.natDegree) := by
  simp only [pathPolynomial, homogenize_map, MvPolynomial.eval_map, MvPolynomial.aeval_def,
    ← coe_eval₂RingHom, MvPolynomial.eval₂_comp_left]
  congr 1
  · ext a
    simp
  · ext i
    fin_cases i <;> simp

/-- If `p` annihilates `u`, then `1 - s + s u` divides `ρ(s)`. -/
private theorem dvd_eval₂_pathPolynomial {S : Type*} [CommRing S] (κ : K →+* S) (p : K[X])
    {s u : S} (hu : p.eval₂ κ u = 0) :
    1 - s + s * u ∣ (pathPolynomial p).eval₂ κ s := by
  have h := sub_mul_dvd_eval_homogenize (p := p.map κ) (by rwa [IsRoot, eval_map])
    natDegree_map_le ![s - 1, s]
  rw [eval₂_pathPolynomial, ← neg_dvd]
  convert h using 1
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

private theorem eval_one_pathPolynomial (p : K[X]) : (pathPolynomial p).eval 1 = p.coeff 0 := by
  rw [← eval₂_id, eval₂_pathPolynomial, Polynomial.map_id, MvPolynomial.eval,
    MvPolynomial.coe_eval₂Hom, eval₂_homogenize_of_eq_one le_rfl (RingHom.id K) ![1 - 1, 1] rfl,
    sub_self, Matrix.cons_val_zero, eval₂_id, coeff_zero_eq_eval_zero]

private theorem eval_zero_pathPolynomial (p : K[X]) :
    (pathPolynomial p).eval 0 = (-1) ^ p.natDegree * p.leadingCoeff := by
  rw [← eval₂_id, eval₂_pathPolynomial, Polynomial.map_id]
  simp only [homogenize, map_sum, MvPolynomial.eval_monomial]
  simp_rw [Finsupp.prod_fintype _ _ (fun _ ↦ pow_zero _), Fin.prod_univ_two]
  rw [Finset.sum_eq_single (p.natDegree, 0)]
  · simp [mul_comm]
  · rintro ⟨i, j⟩ hij hne
    have : j ≠ 0 := by rintro rfl; simp_all
    simp [zero_pow this]
  · simp

end PathPolynomial

variable {k : Type u} {B : Type*} [Field k] [CommRing B] [Algebra k B]

section Path

variable {K : Type*} [Field K] [Algebra k K] (p : K[X]) (u : B ⊗[k] K)

/-- The path `s ↦ 1 - s + s u` in `B ⊗[k] K[s][1/ρ]`, where `ρ = pathPolynomial p`. -/
private noncomputable def pathElement : B ⊗[k] Localization.Away (pathPolynomial p) :=
  1 - 1 ⊗ₜ algebraMap K[X] _ X + 1 ⊗ₜ algebraMap K[X] _ X *
    Algebra.TensorProduct.lTensor (S := B) B (IsScalarTower.toAlgHom k K _) u

/-- If `p` annihilates `u`, viewed in the `K`-algebra `K ⊗[k] B`, then the path `s ↦ 1 - s + s u`
consists of units: it divides the unit `ρ(s)`. -/
private theorem isUnit_pathElement (hpu : aeval (Algebra.TensorProduct.comm k B K u) p = 0) :
    IsUnit (pathElement p u) := by
  let D := Localization.Away (pathPolynomial p)
  let ι : B ⊗[k] K →+* B ⊗[k] D :=
    (Algebra.TensorProduct.lTensor (S := B) B (IsScalarTower.toAlgHom k K D)).toRingHom
  let ψ : K[X] →+* B ⊗[k] D :=
    (Algebra.TensorProduct.includeRight : D →ₐ[k] B ⊗[k] D).toRingHom.comp (algebraMap K[X] D)
  let c : K ⊗[k] B →+* B ⊗[k] D :=
    ι.comp (Algebra.TensorProduct.comm k B K).symm.toRingEquiv.toRingHom
  have hC : ψ.comp C = c.comp (algebraMap K (K ⊗[k] B)) := by
    ext a
    simp [ψ, c, ι, IsScalarTower.algebraMap_apply K K[X] D, Algebra.TensorProduct.algebraMap_apply]
  have hu : p.eval₂ (ψ.comp C) (ι u) = 0 := by
    have h := congrArg c hpu
    rw [aeval_def, Polynomial.hom_eval₂, map_zero, ← hC] at h
    simpa [c] using h
  have hX : ψ X = 1 ⊗ₜ algebraMap K[X] D X := by simp [ψ]
  refine isUnit_of_dvd_unit (dvd_eval₂_pathPolynomial (ψ.comp C) p hu) ?_
  rw [← hX, ← Polynomial.hom_eval₂, eval₂_C_X]
  exact (IsLocalization.Away.algebraMap_isUnit (S := D) (pathPolynomial p)).map
    (Algebra.TensorProduct.includeRight : D →ₐ[k] B ⊗[k] D)

/-- Evaluating the path `s ↦ 1 - s + s u` along a `K`-algebra map `φ : K[s][1/ρ] → K`, that is,
at `s = φ(s)`. -/
private theorem lTensor_pathElement (φ : Localization.Away (pathPolynomial p) →ₐ[K] K) :
    Algebra.TensorProduct.lTensor (S := B) B (φ.restrictScalars k) (pathElement p u) =
      1 - (1 : B) ⊗ₜ[k] φ (algebraMap K[X] _ X) + (1 : B) ⊗ₜ[k] φ (algebraMap K[X] _ X) * u := by
  have hu : Algebra.TensorProduct.lTensor (S := B) B (φ.restrictScalars k)
      (Algebra.TensorProduct.lTensor (S := B) B (IsScalarTower.toAlgHom k K _) u) = u := by
    have h : (Algebra.TensorProduct.lTensor (S := B) B (φ.restrictScalars k)).comp
        (Algebra.TensorProduct.lTensor (S := B) B (IsScalarTower.toAlgHom k K _)) =
          AlgHom.id B (B ⊗[k] K) := by
      ext a'
      simp only [AlgHom.comp_apply, Algebra.TensorProduct.includeRight_apply,
        Algebra.TensorProduct.map_tmul, AlgHom.id_apply, IsScalarTower.coe_toAlgHom',
        AlgHom.coe_restrictScalars']
      exact congrArg _ (φ.commutes a')
    exact AlgHom.congr_fun h u
  simp [pathElement, hu]

end Path

variable [Module.Finite k B]

/-- Every point of `Res_{B/k} 𝔾ₘ` with values in an algebraically closed field `K` is joined to
the identity by a point with values in a domain. Consequently right translation by it fixes every
idempotent of `K ⊗[k] O(Res_{B/k} 𝔾ₘ)`. -/
private theorem rightTranslationAlgHom_eq_self {K : Type u} [Field K] [Algebra k K]
    [IsAlgClosed K] {e : K ⊗[k] WeilRestriction k B B[T;T⁻¹]} (he : IsIdempotentElem e)
    (g : WithConv (K ⊗[k] WeilRestriction k B B[T;T⁻¹] →ₐ[K] K)) :
    HopfAlgebra.rightTranslationAlgHom (k := K) g e = e := by
  let f := (AlgHom.liftEquiv k K _ K).symm g.ofConv
  let u := multiplicativeGroupPoints k B K (toConv f)
  -- the minimal polynomial over `K` of `u`, viewed in the finite `K`-algebra `K ⊗[k] B`
  let v := Algebra.TensorProduct.comm k B K u
  have hv : IsIntegral K v := Algebra.IsIntegral.isIntegral v
  let p := minpoly K v
  have hρ1 : IsUnit ((pathPolynomial p).eval 1) := by
    rw [eval_one_pathPolynomial, isUnit_iff_ne_zero]
    exact minpoly.coeff_zero_ne_zero_of_mem_nonZeroDivisors hv
      (u.isUnit.map (Algebra.TensorProduct.comm k B K)).mem_nonZeroDivisors
  have hρ0 : IsUnit ((pathPolynomial p).eval 0) := by
    rw [eval_zero_pathPolynomial, isUnit_iff_ne_zero]
    exact mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero))
      (leadingCoeff_ne_zero.mpr (minpoly.ne_zero hv))
  have : IsDomain (Localization.Away (pathPolynomial p)) :=
    Localization.Away.isDomain fun h ↦ hρ1.ne_zero (by rw [h, eval_zero])
  -- evaluation of `K[s][1/ρ]` at `s = 1` and at `s = 0`
  let ev₁ := IsLocalization.Away.liftAlgHom (S := Localization.Away (pathPolynomial p))
    (pathPolynomial p) (f := aeval (1 : K)) (by simpa using hρ1)
  let ev₀ := IsLocalization.Away.liftAlgHom (S := Localization.Away (pathPolynomial p))
    (pathPolynomial p) (f := aeval (0 : K)) (by simpa using hρ0)
  -- the point of `Res_{B/k} 𝔾ₘ` over `K[s][1/ρ]` given by the path `s ↦ 1 - s + s u`
  let x := ((multiplicativeGroupPoints k B _).symm
    (isUnit_pathElement p u (minpoly.aeval K v)).unit).ofConv
  have hpath (φ : Localization.Away (pathPolynomial p) →ₐ[K] K) :
      (multiplicativeGroupPoints k B K (toConv ((φ.restrictScalars k).comp x)) : B ⊗[k] K) =
        1 - (1 : B) ⊗ₜ[k] φ (algebraMap K[X] _ X) + (1 : B) ⊗ₜ[k] φ (algebraMap K[X] _ X) * u := by
    rw [multiplicativeGroupPoints_naturality]
    simp [lTensor_pathElement]
  have h₁ : (ev₁.restrictScalars k).comp x = f := by
    refine toConv_injective ((multiplicativeGroupPoints k B K).injective (Units.ext ?_))
    rw [hpath, show ev₁ (algebraMap K[X] _ X) = 1 by simp [ev₁],
      ← Algebra.TensorProduct.one_def]
    ring
  have h₀ : (ev₀.restrictScalars k).comp x =
      (1 : WithConv (WeilRestriction k B B[T;T⁻¹] →ₐ[k] K)).ofConv := by
    refine toConv_injective ((multiplicativeGroupPoints k B K).injective (Units.ext ?_))
    rw [hpath, show ev₀ (algebraMap K[X] _ X) = 0 by simp [ev₀], toConv_ofConv, map_one]
    simp
  have hΨ (φ : Localization.Away (pathPolynomial p) →ₐ[K] K) :
      φ.comp (AlgHom.liftEquiv k K _ _ x) =
        AlgHom.liftEquiv k K _ K ((φ.restrictScalars k).comp x) :=
    Algebra.TensorProduct.ext_ring (AlgHom.ext fun w ↦ by simp)
  refine HopfAlgebra.rightTranslationAlgHom_eq_self_of_path e he g
    (toConv (AlgHom.liftEquiv k K _ _ x)) ev₁ ev₀ ?_ ?_
  · simp [hΨ, h₁, f]
  · simp [hΨ, h₀, ← AlgHom.baseChangePointsMulEquiv_apply_ofConv]

/-- **The Weil restriction of `𝔾ₘ` is geometrically connected.** For a finite-dimensional
commutative algebra `B` over a field `k`, the coordinate Hopf algebra
`WeilRestriction k B B[T;T⁻¹]` of `Res_{B/k} 𝔾ₘ` stays connected after every extension of `k`. -/
theorem geometricallyConnectedCommHopfAlgProperty_multiplicativeGroup :
    geometricallyConnectedCommHopfAlgProperty k
      (CommHopfAlgCat.of k (WeilRestriction k B B[T;T⁻¹])) := by
  rw [geometricallyConnectedCommHopfAlgProperty_iff_connectedSpace_of_isAlgClosed]
  intro K _ _ _
  let W := WeilRestriction k B B[T;T⁻¹]
  suffices ConnectedSpace (PrimeSpectrum (K ⊗[k] W)) by
    let c := Algebra.TensorProduct.comm k W K
    exact c.toRingHom.connectedSpace_primeSpectrum_of_injective c.injective
  exact HopfAlgebra.connectedSpace_primeSpectrum_of_forall_rightTranslationAlgHom_eq_self
    (K := K) (H := K ⊗[k] W) fun _ he g ↦ rightTranslationAlgHom_eq_self he g

end TauCeti.Algebra.WeilRestriction
