/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.ExteriorPower.WedgePairing
public import TauCeti.LinearAlgebra.ExteriorPower.Basis
-- Private: the exterior algebra basis is used only inside the proof of
-- `Set.powersetCard.sign_mul_sign_compl`.
import Mathlib.LinearAlgebra.ExteriorAlgebra.Basis

/-!
# Evaluation formulas for wedge products and pairings

Inside the exterior algebra, the wedge product of exterior powers is the algebra product, and the
wedge product of pure exterior products concatenates their vector families. A trivialisation
in a specified top degree gives the wedge pairing by composing the wedge product with that
trivialisation; the degree transports disappear after identifying the degree with the finrank.
On the exterior-power bases induced by a basis `b`, the wedge pairing of `e_s` and `e_t` is the
shuffle sign of `s` times the volume of `b` when `s` and `t` are disjoint, and zero otherwise.
The top exterior product `Module.Basis.topVector` of a basis indexed by `Fin n` is the wedge of
the basis vectors, and the shuffle signs of a set of `k` indices and of its complement of `l`
indices multiply to `(-1) ^ (k * l)`. Composing a complementary-degree wedge pairing,
trivialised by a linear map on the top exterior power, with the exterior powers of an endomorphism
scales it by the determinant of that endomorphism.
-/

public section

namespace exteriorPower

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] {k l : ℕ}

/-- Inside the exterior algebra, the wedge product of exterior powers is the algebra product. -/
@[simp]
theorem coe_wedge (x : ⋀[R]^k M) (y : ⋀[R]^l M) :
    (wedge R M k l x y : ExteriorAlgebra R M) = x * y :=
  rfl

/-- The wedge product of pure exterior products concatenates their vector families. -/
@[simp 1100]
theorem wedge_ιMulti (u : Fin k → M) (v : Fin l → M) :
    wedge R M k l (ιMulti R k u) (ιMulti R l v) = ιMulti R (k + l) (Fin.append u v) := by
  apply Subtype.ext
  simp only [coe_wedge, ιMulti_apply_coe, ExteriorAlgebra.ιMulti_mul_ιMulti]

/-- The wedge product commutes with applying a linear map to both factors. -/
theorem wedge_map {N : Type*} [AddCommGroup N] [Module R N] (f : M →ₗ[R] N) :
    (wedge R N k l).compl₁₂ (exteriorPower.map k f) (exteriorPower.map l f) =
      (wedge R M k l).compr₂ (exteriorPower.map (k + l) f) := by
  refine exteriorPower.linearMap_ext (R := R) (M := M)
    (N := (⋀[R]^l M) →ₗ[R] ⋀[R]^(k + l) N) (n := k) ?_
  apply AlternatingMap.ext
  intro u
  apply exteriorPower.linearMap_ext
  apply AlternatingMap.ext
  intro v
  simp only [LinearMap.compAlternatingMap_apply, LinearMap.compl₁₂_apply,
    LinearMap.compr₂_apply, exteriorPower.map_apply_ιMulti, exteriorPower.wedge_ιMulti]
  congr 1
  funext i
  refine Fin.addCases ?_ ?_ i <;> intro j <;>
    simp only [Fin.append_left, Fin.append_right, Function.comp_apply]

/-- Pointwise form of `wedge_map` for rewriting evaluations of wedge products. -/
theorem wedge_map_apply {N : Type*} [AddCommGroup N] [Module R N] (f : M →ₗ[R] N)
    (x : ⋀[R]^k M) (y : ⋀[R]^l M) :
    wedge R N k l (exteriorPower.map k f x) (exteriorPower.map l f y) =
      exteriorPower.map (k + l) f (wedge R M k l x y) :=
  LinearMap.congr_fun₂ (wedge_map f) x y

/-- A wedge pairing transported from a specified top degree is the wedge product followed by
the trivialisation in that degree. -/
theorem wedgePairing_eq_compr₂_of_finrank_eq (n : ℕ) (hfin : Module.finrank R M = n)
    (hdeg : k + l = n) (vol : (⋀[R]^n M) ≃ₗ[R] R) :
    wedgePairing
        ((LinearEquiv.ofEq (⋀[R]^(Module.finrank R M) M) (⋀[R]^n M)
          (congrArg (fun d ↦ ⋀[R]^d M) hfin)).trans vol) (hdeg.trans hfin.symm) =
      (wedge R M k l).compr₂ (hdeg ▸ vol) := by
  subst n
  rfl

/-- For a free module of finrank `n = k + l` and any linear functional `vol` on `⋀^n M`,
precomposing `wedge` followed by `vol` with the exterior powers of an endomorphism `f` scales it
by `det f`. -/
theorem
    wedge_compr₂_compl₁₂_exteriorPower_map_eq_det_smul [Module.Free R M]
    (hn : Module.finrank R M = n) (hkl : k + l = n) (vol : ⋀[R]^n M →ₗ[R] R)
    (f : M →ₗ[R] M) :
    LinearMap.compl₁₂ ((wedge R M k l).compr₂ (hkl ▸ vol))
      (exteriorPower.map k f) (exteriorPower.map l f) =
      LinearMap.det f • ((wedge R M k l).compr₂ (hkl ▸ vol)) := by
  apply LinearMap.ext
  intro x
  apply LinearMap.ext
  intro y
  simp only [LinearMap.compl₁₂_apply, LinearMap.smul_apply, LinearMap.compr₂_apply]
  rw [wedge_map_apply]
  subst n
  have htop := LinearMap.map_exteriorPower_finrank_eq_det_smul f
  rw [← hkl] at htop
  rw [htop]
  simp only [LinearMap.smul_apply, map_smul, LinearMap.id_apply, smul_eq_mul]

/-- **The wedge pairing on exterior-power basis vectors**: `e_s` and `e_t` pair to the shuffle sign
of `s` times the volume `vol b.topVector` when `s` and `t` are disjoint, and to zero otherwise.
This is the entrywise form of Mathlib's `exteriorPower.wedgePairing_eq_apply_topVector_smul`. -/
theorem wedgePairing_exteriorPower_apply [Nontrivial R] (vol : ⋀[R]^(Module.finrank R M) M ≃ₗ[R] R)
    (hkl : k + l = Module.finrank R M) {ι : Type*} [LinearOrder ι] [Fintype ι]
    (b : Module.Basis ι R M) (s : Set.powersetCard ι k) (t : Set.powersetCard ι l) :
    wedgePairing vol hkl (b.exteriorPower k s) (b.exteriorPower l t) =
      Set.powersetCard.sign s • vol b.topVector • if Disjoint s.val t.val then 1 else 0 := by
  have hkl' : k + l = Fintype.card ι := by rw [hkl, Module.finrank_eq_card_basis b]
  rw [wedgePairing_eq_apply_topVector_smul vol hkl b]
  simp [-Module.Basis.coe_dualBasis, -coe_basis, Module.Basis.groupSMul_apply,
    Module.Basis.dualBasis_apply_self, Equiv.eq_symm_apply, eq_comm (b := s),
    Set.powersetCard.disjoint_iff_eq_compl hkl']

/-- The top exterior product of a basis indexed by `Fin n` is the wedge of the basis vectors in
their given order, read in the degree `finrank R M = n`. -/
theorem _root_.Module.Basis.topVector_eq_ιMulti [Nontrivial R] {n : ℕ}
    (h : Module.finrank R M = n) (b : Module.Basis (Fin n) R M) :
    b.topVector = ιMulti R _ (b ∘ finCongr h) := by
  -- The increasing enumeration of `Finset.univ` is the unique order embedding into `Fin n`.
  set s : Set.powersetCard (Fin n) (Module.finrank R M) :=
    ⟨Finset.univ, by simp [Module.finrank_eq_card_basis b]⟩
  have he : Set.powersetCard.ofFinEmbEquiv.symm s = (Fin.castOrderIso h).toOrderEmbedding := by
    refine OrderEmbedding.eq_of_range_eq ?_
    ext i
    simpa using (Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem s i).2 (Finset.mem_univ i)
  rw [← b.topVector_eq_exteriorPower s, basis_apply, ιMulti_family, he]
  simp [Function.comp_def]

end exteriorPower

namespace Set.powersetCard

/-- **The shuffle signs of complementary index sets**: for a set `s` of `k` indices whose
complement has `l` indices, `sign s * sign sᶜ = (-1) ^ (k * l)`. The two shuffles differ by moving
the block `sᶜ` past the block `s`. -/
theorem sign_mul_sign_compl {I : Type*} [LinearOrder I] [Fintype I] {k l : ℕ}
    (h : l + k = Fintype.card I) (s : powersetCard I k) :
    powersetCard.sign s * powersetCard.sign (compl h s) = (-1) ^ (k * l) := by
  -- Compare `e_s ∧ e_{sᶜ}` and `e_{sᶜ} ∧ e_s` in the exterior algebra of `I → ℤ`, where they are
  -- `sign s` and `sign sᶜ` times the top basis vector.
  set t := compl h s
  have h' : k + l = Fintype.card I := by omega
  have hst : Disjoint s.val t.val :=
    (disjoint_iff_eq_compl h').2 ((compl h).symm_apply_apply s).symm
  set b := Pi.basisFun ℤ I
  -- Both products of `e_s` and `e_t` are signed copies of the top basis vector `e_univ`.
  have hmul : ∀ {m n : ℕ} (hmn : m + n = Fintype.card I) (u : powersetCard I m)
      (v : powersetCard I n) (huv : Disjoint u.val v.val),
      b.ExteriorAlgebra u * b.ExteriorAlgebra v =
        powersetCard.sign u • b.ExteriorAlgebra Finset.univ := fun hmn u v huv ↦ by
    have hunion : (disjUnion huv : Finset I) = Finset.univ :=
      Finset.eq_univ_of_card _ <| by
        rw [coe_disjUnion, Finset.card_disjUnion, mem_iff.1 u.2, mem_iff.1 v.2, hmn]
    rw [ExteriorAlgebra.basis_mul_of_disjoint b u v huv,
      ← sign_eq_permOfDisjoint_sign hmn u v huv, hunion]
  -- Exterior products of degrees `k` and `l` commute up to `(-1) ^ (l * k)`.
  have hcomm : b.ExteriorAlgebra s * b.ExteriorAlgebra t =
      (-1 : ℤˣ) ^ (l * k) • (b.ExteriorAlgebra t * b.ExteriorAlgebra s) := by
    simp only [ExteriorAlgebra.basis_apply_powersetCard, ExteriorAlgebra.ιMulti_family]
    exact ExteriorAlgebra.ιMulti_mul_ιMulti_anticomm (R := ℤ) _ _
  rw [hmul h' s t hst, hmul h t s hst.symm, smul_smul] at hcomm
  -- Comparing the coefficients of `e_univ` gives `sign s = (-1) ^ (l * k) * sign t`.
  have hcoef := congrArg (fun x ↦ b.ExteriorAlgebra.repr x Finset.univ) hcomm
  simp only [Units.smul_def, map_zsmul, Finsupp.smul_apply, Module.Basis.repr_self,
    Finsupp.single_eq_same, smul_eq_mul, mul_one] at hcoef
  rw [Units.ext hcoef, mul_assoc, Int.units_mul_self, mul_one, mul_comm]

end Set.powersetCard
