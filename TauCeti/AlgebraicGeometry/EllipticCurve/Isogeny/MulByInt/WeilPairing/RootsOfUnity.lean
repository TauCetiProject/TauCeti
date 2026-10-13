/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.MulByInt.Torsion.Structure
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.MulByInt.WeilPairing.Galois
public import TauCeti.RingTheory.RootsOfUnity.ZMod
-- Proof-only: the fixed field of all automorphisms of a Galois extension is the base field.
import Mathlib.FieldTheory.Galois.Infinite

/-!
# The Weil pairing takes primitive values

Let `W` be an elliptic curve over a separably closed field `F` and `N` a positive integer
invertible in `F`. The Weil pairing `e_N` on `E[N]` takes a primitive `N`-th root of unity as a
value (Silverman III.8.1.1). In a basis `(P, Q)` of `E[N]` over `ZMod N`, bilinearity and the
alternating property give `e_N(P, a • P + c • Q) = c • e_N(P, Q)`, so if `r • e_N(P, Q) = 0` then
`r • P` pairs trivially with all of `E[N]`, and nondegeneracy forces `r = 0`. Hence `e_N(P, Q)` is
a primitive `N`-th root of unity, and `e_N(P, ·)` maps `E[N]` onto `μ_N`.

Combined with Galois equivariance, `e_N(σ S, σ T) = σ (e_N(S, T))`, this shows that over any field
`F`, with `K` a separably closed extension, an `F`-automorphism of `K` acting trivially on `E[N]`
fixes every `N`-th root of unity in `K`. When `K` is Galois over `F`, for instance a separable
closure, and the Galois action on `E[N]` is trivial, `F` itself contains a primitive `N`-th root of
unity: if `E[N] ⊆ E(F)` then `μ_N ⊆ F`. Over a field containing `E[N]`, both `E[N]` and `μ_N` are
then trivial Galois modules, so `E[N] ≅ μ_N × μ_N`; this is how Kummer theory enters the weak
Mordell–Weil theorem and the finiteness of the `N`-Selmer group (Silverman VIII.1.2 and X.4.2).

## Main results

* `TauCeti.Isogeny.exists_isPrimitiveRoot_weilPairing`: some value `e_N(S, T)` is a primitive
  `N`-th root of unity.
* `TauCeti.Isogeny.exists_surjective_weilPairing`: for some `S`, the map `e_N(S, ·)` is onto `μ_N`.
* `WeierstrassCurve.algEquiv_apply_eq_self_of_torsionGaloisAction_eq_one`: an automorphism acting
  trivially on `E[N]` fixes the `N`-th roots of unity.
* `WeierstrassCurve.exists_isPrimitiveRoot_of_forall_torsionGaloisAction_eq_one`: if the Galois
  action on `E[N]` is trivial, the base field contains a primitive `N`-th root of unity.
* `WeierstrassCurve.exists_isPrimitiveRoot_of_card_torsionBy`: if `E(F)` has `N²` points of order
  dividing `N`, that is `E[N] ⊆ E(F)`, then `F` contains a primitive `N`-th root of unity.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.8.1.1, VIII.1.2 and
  X.4.2.
-/

public section

open WeierstrassCurve

namespace TauCeti.Isogeny

variable {F : Type*} [Field F] [DecidableEq F] [IsSepClosed F] (W : WeierstrassCurve F)
  [W.IsElliptic] (N : ℕ) [NeZero N] (hN : (N : F) ≠ 0)

/-- On a basis `(P, Q)` of `E[N]`, no nonzero scalar kills `e_N(P, Q)`: if `r • e_N(P, Q) = 0`,
then `r • P` pairs trivially with every `T = a • P + c • Q`, since `e_N(P, T) = c • e_N(P, Q)`. -/
private theorem eq_zero_of_smul_weilPairing_eq_zero
    (b : Module.Basis (Fin 2) (ZMod N) (AddSubgroup.torsionBy W.toAffine.Point (N : ℤ)))
    {r : ZMod N} (hr : r • weilPairing W N hN (b 0) (b 1) = 0) : r = 0 := by
  -- the pairing is `ZMod N`-linear in each variable. Its domain is written `Submodule.torsionBy`,
  -- while the `ZMod N`-module structure is on `AddSubgroup.torsionBy`, the same subtype of points,
  -- so `M` is named for `ZMod.map_smul`.
  have hl (S T : AddSubgroup.torsionBy W.toAffine.Point (N : ℤ)) (c : ZMod N) :
      weilPairing W N hN (c • S) T = c • weilPairing W N hN S T := by
    rw [← AddMonoidHom.flip_apply, ZMod.map_smul (M := AddSubgroup.torsionBy W.toAffine.Point _),
      AddMonoidHom.flip_apply]
  have hr' (S T : AddSubgroup.torsionBy W.toAffine.Point (N : ℤ)) (c : ZMod N) :
      weilPairing W N hN S (c • T) = c • weilPairing W N hN S T :=
    ZMod.map_smul (M := AddSubgroup.torsionBy W.toAffine.Point _) _ c T
  have h : r • b 0 = 0 := by
    refine weilPairing_nondegenerate W N hN fun T ↦ ?_
    -- `T`, read in the `ZMod N`-module `AddSubgroup.torsionBy`, to expand it in the basis `b`
    let T' : AddSubgroup.torsionBy W.toAffine.Point (N : ℤ) := T
    have hT : weilPairing W N hN (b 0) T' = b.repr T' 1 • weilPairing W N hN (b 0) (b 1) := by
      conv_lhs => rw [← b.sum_repr T']
      rw [map_sum, Fin.sum_univ_two, hr', hr', weilPairing_self, smul_zero, zero_add]
    calc weilPairing W N hN (r • b 0) T = r • weilPairing W N hN (b 0) T' := hl _ _ _
      _ = 0 := by rw [hT, smul_comm, hr, smul_zero]
  exact b.linearIndependent.smul_left_injective 0 (h.trans (zero_smul _ _).symm)

/-- **The Weil pairing takes a primitive `N`-th root of unity as a value** (Silverman III.8.1.1),
over a separably closed field in which `N` is invertible. -/
theorem exists_isPrimitiveRoot_weilPairing :
    ∃ S T : Submodule.torsionBy ℤ W.toAffine.Point (N : ℤ),
      IsPrimitiveRoot (((weilPairing W N hN S T).toMul : Fˣ) : F) N := by
  obtain ⟨b⟩ := nonempty_basis_torsionBy W N hN
  refine ⟨b 0, b 1, IsPrimitiveRoot.coe_units_iff.2 <|
    IsPrimitiveRoot.coe_submonoidClass_iff.2
      ⟨by rw [← toMul_nsmul, nsmul_additive_rootsOfUnity_eq_zero, toMul_zero],
      fun l hl ↦ (ZMod.natCast_eq_zero_iff l N).1 <|
        eq_zero_of_smul_weilPairing_eq_zero W N hN b ?_⟩⟩
  rw [Nat.cast_smul_eq_nsmul]
  exact Additive.toMul.injective (by simpa [toMul_nsmul] using hl)

/-- **The Weil pairing is onto `μ_N` in its second variable** for a suitable first argument, over
a separably closed field in which `N` is invertible. -/
theorem exists_surjective_weilPairing :
    ∃ S : Submodule.torsionBy ℤ W.toAffine.Point (N : ℤ),
      Function.Surjective (weilPairing W N hN S) := by
  obtain ⟨S, T, hST⟩ := exists_isPrimitiveRoot_weilPairing W N hN
  have h := IsPrimitiveRoot.coe_units_iff.1 hST
  refine ⟨S, fun x ↦ ?_⟩
  obtain ⟨i, rfl⟩ := h.zmodEquivRootsOfUnity.surjective x
  -- `e_N(S, i • T) = ζ ^ i`, which is the image of `i` under `h.zmodEquivRootsOfUnity`
  refine ⟨i.val • T, Additive.toMul.injective (Subtype.ext ?_)⟩
  rw [map_nsmul, toMul_nsmul, SubmonoidClass.coe_pow,
    ← h.coe_zmodEquivRootsOfUnity_apply_natCast i.val, ZMod.natCast_zmod_val]

end TauCeti.Isogeny

namespace WeierstrassCurve

open TauCeti.Isogeny

variable {F : Type*} [Field F] (W : WeierstrassCurve F) [W.IsElliptic] {N : ℕ} [NeZero N]

section Galois

variable {K : Type*} [Field K] [DecidableEq K] [Algebra F K] [IsSepClosed K] (hN : (N : K) ≠ 0)

include hN in
/-- **An automorphism acting trivially on `E[N]` fixes the `N`-th roots of unity**: for an
`F`-automorphism `σ` of a separably closed field `K` in which `N` is invertible, if `σ` fixes
every `N`-torsion point of `W` over `K`, then `σ ζ = ζ` for every `ζ ∈ K` with `ζ ^ N = 1`. -/
theorem algEquiv_apply_eq_self_of_torsionGaloisAction_eq_one {σ : K ≃ₐ[F] K}
    (hσ : W.torsionGaloisAction N σ = 1) {ζ : K} (hζ : ζ ^ N = 1) : σ ζ = ζ := by
  obtain ⟨S, hS⟩ := exists_surjective_weilPairing (W⁄K) N hN
  obtain ⟨T, hT⟩ := hS (Additive.ofMul (rootsOfUnity.mkOfPowEq ζ hζ))
  have h := weilPairing_torsionGaloisAction W N hN σ S T
  rw [hσ, toAdd_one, AddAut.zero_apply, AddAut.zero_apply, hT] at h
  simpa using congrArg (fun x ↦ (((Additive.toMul x : rootsOfUnity N K) : Kˣ) : K)) h.symm

include hN in
/-- **If the Galois action on `E[N]` is trivial, the base field contains a primitive `N`-th root
of unity** (Silverman III.8.1.1): for a separably closed Galois extension `K` of `F`, such as a
separable closure, in which `N` is invertible, if every `F`-automorphism of `K` fixes the
`N`-torsion of `W` over `K`, then `F` contains a primitive `N`-th root of unity. -/
theorem exists_isPrimitiveRoot_of_forall_torsionGaloisAction_eq_one [IsGalois F K]
    (h : ∀ σ : K ≃ₐ[F] K, W.torsionGaloisAction N σ = 1) : ∃ ζ : F, IsPrimitiveRoot ζ N := by
  obtain ⟨S, T, hST⟩ := exists_isPrimitiveRoot_weilPairing (W⁄K) N hN
  obtain ⟨ζ, hζ⟩ := (InfiniteGalois.mem_range_algebraMap_iff_fixed _).2 fun σ ↦
    W.algEquiv_apply_eq_self_of_torsionGaloisAction_eq_one hN (h σ) hST.pow_eq_one
  exact ⟨ζ, (IsPrimitiveRoot.map_iff_of_injective (algebraMap F K).injective).1 (hζ ▸ hST)⟩

end Galois

/-- **If `E[N] ⊆ E(F)` then `μ_N ⊆ F`** (Silverman III.8.1.1): if an elliptic curve over `F` has
`N²` rational `N`-torsion points, with `N` invertible in `F`, then `F` contains a primitive `N`-th
root of unity. -/
theorem exists_isPrimitiveRoot_of_card_torsionBy [DecidableEq F] (hN : (N : F) ≠ 0)
    (h : Nat.card (AddSubgroup.torsionBy W.toAffine.Point (N : ℤ)) = N ^ 2) :
    ∃ ζ : F, IsPrimitiveRoot ζ N := by
  classical
  let K := SeparableClosure F
  have hNK : (N : K) ≠ 0 := by rwa [← map_natCast (algebraMap F K), map_ne_zero]
  -- the inclusion `E(F) → E(K)`; `WeierstrassCurve.Affine.pointMap` is the same map, but stated
  -- for the classical decidable equality on `F`, not the one the torsion subgroup in `h` uses
  let f : W.toAffine.Point →+ (W⁄K).toAffine.Point :=
    (Affine.Point.map (W' := W.toAffine) (Algebra.ofId F K)).comp
      (Affine.Point.equivBaseChangeSelf W.toAffine).toAddMonoidHom
  have hf : Function.Injective f :=
    (Affine.Point.map_injective _).comp (Affine.Point.equivBaseChangeSelf W.toAffine).injective
  -- it carries `E[N](F)` onto `E[N](K)`, since both have `N²` points
  obtain ⟨b⟩ := nonempty_basis_torsionBy (W⁄K) N hNK
  have : Finite (AddSubgroup.torsionBy (W⁄K).toAffine.Point (N : ℤ)) :=
    Finite.of_equiv (Fin 2 → ZMod N) b.equivFun.symm.toEquiv
  have hmap : (AddSubgroup.torsionBy W.toAffine.Point (N : ℤ)).map f =
      AddSubgroup.torsionBy (W⁄K).toAffine.Point (N : ℤ) := by
    refine AddSubgroup.eq_of_le_of_card_ge ?_ ?_
    · rintro _ ⟨P, hP, rfl⟩
      exact AddSubgroup.torsionBy.nsmul_iff.2 <| by
        rw [← map_nsmul, AddSubgroup.torsionBy.nsmul_iff.1 hP, map_zero]
    · rw [Nat.card_congr b.equivFun.toEquiv, AddSubgroup.card_map_of_injective hf, h,
        Nat.card_fun, Nat.card_zmod, Nat.card_fin]
  -- so every `F`-automorphism of `K` fixes `E[N](K)`
  refine exists_isPrimitiveRoot_of_forall_torsionGaloisAction_eq_one (K := K) W hNK fun σ ↦
    Multiplicative.toAdd.injective <| AddEquiv.ext fun T ↦ Subtype.ext ?_
  obtain ⟨P, -, hP⟩ := hmap.ge T.2
  rw [torsionGaloisAction_apply_coe, pointGaloisAction_apply, toAdd_one, AddAut.zero_apply, ← hP]
  simp only [f, AddMonoidHom.comp_apply, Affine.Point.map_map]
  rw [Subsingleton.elim (σ.toAlgHom.comp (Algebra.ofId F K)) (Algebra.ofId F K)]

end WeierstrassCurve

end
