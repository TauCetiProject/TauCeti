/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.TrivialFp
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Cup.Functoriality
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Cup.Graded.Comm
import Mathlib.Algebra.Field.ZMod

/-!
# The cup product with trivial `ZMod p` coefficients

Multiplication in `ZMod p` gives a continuous equivariant pairing of the trivial coefficient
representations. Its cup product in degrees `(1, 1)` is the bilinear pairing on continuous
cohomology used to define and study Demushkin groups. The coefficient representation is lifted
to the universe of the group, as required by the continuous cohomology complex. When `p` is
prime, `ZMod p` is the field `𝔽_p`.

Because multiplication is commutative the opposite pairing of `fpPairing p G` is itself, and
graded commutativity of the cup product in bidegree `(1, 1)` reads `cupFp p G a b = - cupFp p G b a`
(`TauCeti.cupFp_gradedComm`). Consequently `a ⌣ b` vanishes exactly when `b ⌣ a` does, and at an
odd prime every cup square `a ⌣ a` vanishes, since `2` is then invertible in `𝔽_p`.

## Main definitions

* `TauCeti.fpPairing`: multiplication on the trivial coefficient representation.
* `TauCeti.cupFp`: the resulting cup product `H¹(G, ZMod p) × H¹(G, ZMod p) → H²(G, ZMod p)`.

## Main results

* `TauCeti.cupFp_res`: restriction to a subgroup preserves `cupFp`.
* `TauCeti.cupFp_map`: a continuous group homomorphism preserves `cupFp`.
* `TauCeti.cupFp_bijective_iff_of_bijective`: perfectness of `cupFp` transfers along a continuous
  homomorphism inducing isomorphisms on `H¹` and `H²`.
* `TauCeti.cupFp_bijective_congr`: perfectness of `cupFp` is invariant under topological group
  isomorphism.
* `TauCeti.fpPairing_flip`: the opposite of the multiplication pairing is itself.
* `TauCeti.cupFp_gradedComm`: the cup square is graded-commutative, `cupFp a b = - cupFp b a`.
* `TauCeti.cupFp_eq_zero_comm`: `a ⌣ b = 0` exactly when `b ⌣ a = 0`.
* `TauCeti.cupFp_self_eq_zero_of_ne_two`: at an odd prime every cup square `a ⌣ a` vanishes.

## References

* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, I §1.4.
* J.-P. Serre, *Galois Cohomology*, Springer (1997), Chapter I, §4.5.
* J. Labute, *Classification of Demushkin groups*, Canad. J. Math. 19 (1967), 106–132, §1.
-/

public section

namespace TauCeti

open CategoryTheory _root_.ContinuousCohomology

universe u

section Monoid

variable (p : ℕ) (G : Type u) [Monoid G]

/-- Multiplication of trivial `ZMod p` coefficients as a continuous equivariant
bilinear pairing. -/
noncomputable def fpPairing :
    TopPairing (trivialFp p G) (trivialFp p G) (trivialFp p G) where
  bil := (((LinearMap.mul (ZMod p) (ZMod p)).comp
    (trivialFpEquiv p G).toLinearMap).compl₂
      (trivialFpEquiv p G).toLinearMap).compr₂
        (trivialFpEquiv p G).symm.toLinearMap
  cont := continuous_of_discreteTopology
  equivariant g x y := by simp

/-- The coefficient pairing is multiplication in `ZMod p`, under the universe lift. -/
@[simp]
theorem fpPairing_bil_apply (x y : (trivialFp p G).V) :
    (fpPairing p G).bil x y =
      (trivialFpEquiv p G).symm (trivialFpEquiv p G x * trivialFpEquiv p G y) :=
  by simp [fpPairing]

/-- Multiplication on the trivial coefficient representation is symmetric. -/
theorem fpPairing_bil_comm (x y : (trivialFp p G).V) :
    (fpPairing p G).bil x y = (fpPairing p G).bil y x := by
  simp only [fpPairing_bil_apply, mul_comm]

/-- The opposite of the multiplication pairing is itself, because multiplication in `ZMod p` is
commutative. -/
@[simp]
theorem fpPairing_flip : (fpPairing p G).flip = fpPairing p G :=
  TopPairing.ext (LinearMap.ext₂ fun x y ↦ by
    rw [TopPairing.flip_bil, fpPairing_bil_comm])

end Monoid

section Group

variable (p : ℕ) (G : Type u) [Group G]

/-- Transport along `res_trivialFp` intertwines the restricted multiplication pairing of `G` with
the multiplication pairing of `S`. -/
theorem eqToHom_res_fpPairing_bil (S : Subgroup G)
    (x y : (TopRep.res (S.subtype : S →* G) (trivialFp p G)).V) :
    eqToHom (res_trivialFp p G S) (((fpPairing p G).res S.subtype).bil x y) =
      (fpPairing p S).bil (eqToHom (res_trivialFp p G S) x) (eqToHom (res_trivialFp p G S) y) :=
  (trivialFpEquiv p S).injective (by
    -- the transport lemma is passed with `p G S` fixed: by bare name, `simp` indexes it through
    -- the unfolded restricted carrier and does not find it in this module
    simp only [trivialFpEquiv_eqToHom_res_trivialFp p G S, TopPairing.res_bil,
      fpPairing_bil_apply, LinearEquiv.apply_symm_apply])

variable [TopologicalSpace G] [IsTopologicalGroup G]

/-- The degree-`(1,1)` cup product on continuous cohomology with trivial `ZMod p` coefficients. -/
noncomputable def cupFp :
    cohomFp p G 1 →ₗ[ZMod p] cohomFp p G 1 →ₗ[ZMod p] cohomFp p G 2 :=
  (fpPairing p G).cup 1 1

/-- The specialized cup product is the general cup product of the multiplication pairing.
This equation lets general cup-product results apply to arbitrary cohomology classes. -/
theorem cupFp_def : cupFp p G = (fpPairing p G).cup 1 1 := by
  simp only [cupFp]

/-- On classes of cocycles, `cupFp` is the class of their cochain cup product. -/
@[simp]
theorem cupFp_π (a b : cocycles (trivialFp p G) 1) :
    cupFp p G (π (trivialFp p G) 1 a)
      (π (trivialFp p G) 1 b) =
        π (trivialFp p G) 2 ((fpPairing p G).cupCocycles 1 1 a b) := by
  simpa [cupFp_def] using (fpPairing p G).cup_π 1 1 a b

/-- A continuous group homomorphism preserves the cup product with trivial `ZMod p`
coefficients. -/
@[simp]
theorem cupFp_map {H : Type u} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    (φ : H →ₜ* G) (a b : cohomFp p G 1) :
    cohomFpMap p φ 2 (cupFp p G a b) =
      cupFp p H (cohomFpMap p φ 1 a) (cohomFpMap p φ 1 b) := by
  have hpair (x y : (trivialFp p G).V) :
      eqToHom (res_trivialFp_hom p φ) ((fpPairing p G).bil x y) =
        (fpPairing p H).bil (eqToHom (res_trivialFp_hom p φ) x)
          (eqToHom (res_trivialFp_hom p φ) y) := by
    apply (trivialFpEquiv p H).injective
    simp only [trivialFpEquiv_eqToHom_res_trivialFp_hom p φ,
      fpPairing_bil_apply, LinearEquiv.apply_symm_apply]
  simpa only [cohomFpMap_def, cupFp_def, one_add_one_eq_two] using
    (fpPairing p G).cup_map (fpPairing p H) φ
      (eqToHom (res_trivialFp_hom p φ))
      (eqToHom (res_trivialFp_hom p φ))
      (eqToHom (res_trivialFp_hom p φ)) hpair 1 1 a b

/-- **Perfectness of the cup square transfers along a continuous homomorphism** `φ : H →ₜ* G`
inducing isomorphisms on `H¹(-, ZMod p)` and `H²(-, ZMod p)`: `cupFp p G` is a bijection onto the
linear maps `H¹(G, ZMod p) →ₗ H²(G, ZMod p)` exactly when `cupFp p H` is. -/
theorem cupFp_bijective_iff_of_bijective {H : Type u} [Group H] [TopologicalSpace H]
    [IsTopologicalGroup H] (φ : H →ₜ* G) (h₁ : Function.Bijective (cohomFpMap p φ 1))
    (h₂ : Function.Bijective (cohomFpMap p φ 2)) :
    Function.Bijective (cupFp p G) ↔ Function.Bijective (cupFp p H) := by
  let e₁ := LinearEquiv.ofBijective (cohomFpMap p φ 1).hom.toLinearMap h₁
  let e₂ := LinearEquiv.ofBijective (cohomFpMap p φ 2).hom.toLinearMap h₂
  -- `cupFp p H` is `cupFp p G` conjugated by the cohomology equivalences along `φ`
  have h : ⇑(cupFp p H) = (e₁.arrowCongr e₂) ∘ cupFp p G ∘ e₁.symm :=
    funext fun a => LinearMap.ext fun b => by
      rw [Function.comp_apply, Function.comp_apply, LinearEquiv.arrowCongr_apply]
      conv_lhs => rw [← e₁.apply_symm_apply a, ← e₁.apply_symm_apply b]
      exact (cupFp_map p G φ _ _).symm
  rw [h, EquivLike.comp_bijective, EquivLike.bijective_comp]

/-- **Perfectness of the cup square is invariant under topological group isomorphism**: `cupFp p G`
is a bijection onto the linear maps `H¹(G, ZMod p) →ₗ H²(G, ZMod p)` exactly when `cupFp p H` is,
for `G ≃ₜ* H`. -/
theorem cupFp_bijective_congr {H : Type u} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    (e : G ≃ₜ* H) : Function.Bijective (cupFp p G) ↔ Function.Bijective (cupFp p H) :=
  have h (n : ℕ) :
      Function.Bijective (cohomFpMap p (ContinuousMonoidHom.toContinuousMonoidHom e.symm) n) :=
    funext (cohomFpLinearEquiv_apply p e n) ▸ (cohomFpLinearEquiv p e n).bijective
  cupFp_bijective_iff_of_bijective p G _ (h 1) (h 2)

/-- **Restriction preserves the cup product with trivial `ZMod p` coefficients**:
`res (a ⌣ b) = res a ⌣ res b` for the named restriction `trivialFpResMap`. -/
@[simp]
theorem cupFp_res (S : Subgroup G) (a b : cohomFp p G 1) :
    trivialFpResMap p G S 2 (cupFp p G a b) =
      cupFp p S (trivialFpResMap p G S 1 a) (trivialFpResMap p G S 1 b) := by
  simpa only [← cohomFpMap_subgroupSubtype] using
    cupFp_map p G (ContinuousMonoidHom.subgroupSubtype S) a b

/-- **Graded commutativity of the cup square**, `cupFp a b = - cupFp b a`: the bidegree-`(1, 1)`
graded commutativity of the cup product at the multiplication pairing, whose opposite pairing is
itself. -/
theorem cupFp_gradedComm (a b : cohomFp p G 1) : cupFp p G a b = -cupFp p G b a := by
  rw [cupFp_def, (fpPairing p G).cup_gradedComm 1 1 a b, ContinuousCohomology.degreeCast_rfl,
    Iso.refl_hom, ConcreteCategory.id_apply, mul_one, pow_one, neg_one_smul, fpPairing_flip]

/-- `a ⌣ b` vanishes exactly when `b ⌣ a` does, by graded commutativity. -/
theorem cupFp_eq_zero_comm (a b : cohomFp p G 1) : cupFp p G a b = 0 ↔ cupFp p G b a = 0 := by
  rw [cupFp_gradedComm, neg_eq_zero]

/-- **At an odd prime every cup square vanishes**: `a ⌣ a = -(a ⌣ a)` and `2` is invertible. -/
theorem cupFp_self_eq_zero_of_ne_two [Fact p.Prime] (hp : p ≠ 2) (a : cohomFp p G 1) :
    cupFp p G a a = 0 := by
  have h2 : (2 : ZMod p) ≠ 0 := CharP.cast_ne_zero_of_ne_of_prime (ZMod p) Nat.prime_two hp
  have h : (2 : ZMod p) • cupFp p G a a = 0 := by
    rw [two_smul]
    exact add_eq_zero_iff_eq_neg.mpr (cupFp_gradedComm p G a a)
  exact (smul_eq_zero.mp h).resolve_left h2

end Group

end TauCeti
