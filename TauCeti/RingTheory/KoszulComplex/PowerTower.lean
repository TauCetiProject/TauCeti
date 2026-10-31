/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.KoszulComplex.Basic
public import TauCeti.LinearAlgebra.ExteriorPower.Basis

/-!
# The tower of Koszul complexes of powers

For a finite family `x : ι → R`, the complexes `K(xᵢⁿ)` form an inverse system. The transition
from exponent `m` to exponent `n ≤ m` is the exterior power of the diagonal map
`eᵢ ↦ xᵢ^(m-n) eᵢ`. In particular it is the identity in degree zero, and multiplication by
`xᵢ` on the `i`th degree-one generator for successive exponents.

The image estimate in positive degrees measures the transitions in ideal-adic filtrations.
It is used with Artin–Rees to prove that higher Koszul homology is pro-zero over Noetherian
rings. The exponent zero is included; no regularity of the family is required.

The construction uses `TauCeti.koszulComplex.map` and the diagonal action formula for exterior
powers in `TauCeti.LinearAlgebra.ExteriorPower.Basis`.

## References

* The Stacks Project, Tags 0920 and 0921.
-/

public section

noncomputable section

open CategoryTheory Opposite

namespace TauCeti.koszulComplex

universe u v

variable {R : Type u} [CommRing R] {ι : Type v} [Fintype ι] (x : ι → R)

/-- The transition `K(xᵢᵐ) → K(xᵢⁿ)` for `n ≤ m`. -/
def powerMap {n m : ℕ} (h : n ≤ m) :
    koszulComplex (Fintype.linearCombination R (fun i ↦ x i ^ m)) ⟶
      koszulComplex (Fintype.linearCombination R (fun i ↦ x i ^ n)) :=
  map (LinearMap.mulLeft R (x ^ (m - n))) (by
    ext v
    simp only [LinearMap.comp_apply, Fintype.linearCombination_apply,
      LinearMap.mulLeft_apply, Pi.mul_apply, Pi.pow_apply, smul_eq_mul]
    apply Finset.sum_congr rfl
    intro i _
    rw [mul_right_comm, ← pow_add, Nat.sub_add_cancel h, mul_comm])

/-- In degree `k` the power transition is the `k`th exterior power of its diagonal map. -/
theorem powerMap_f {n m : ℕ} (h : n ≤ m) (k : ℕ) :
    (powerMap x h).f k =
      ModuleCat.ofHom (exteriorPower.map k (LinearMap.mulLeft R (x ^ (m - n)))) := by
  rw [powerMap, map_f]

@[simp]
theorem powerMap_refl (n : ℕ) : powerMap x (le_refl n) = 𝟙 _ := by
  simp [powerMap, LinearMap.mulLeft_one]

/-- Power transitions compose in the quotient direction. -/
@[reassoc]
theorem powerMap_comp {n m l : ℕ} (hnm : n ≤ m) (hml : m ≤ l) :
    powerMap x hml ≫ powerMap x hnm = powerMap x (hnm.trans hml) := by
  ext k : 1
  simp only [HomologicalComplex.comp_f, powerMap_f]
  have hd : LinearMap.mulLeft R (x ^ (m - n)) ∘ₗ LinearMap.mulLeft R (x ^ (l - m)) =
      LinearMap.mulLeft R (x ^ (l - n)) := by
    rw [← LinearMap.mulLeft_mul, ← pow_add]
    congr 2
    omega
  have he : exteriorPower.map k (LinearMap.mulLeft R (x ^ (m - n))) ∘ₗ
      exteriorPower.map k (LinearMap.mulLeft R (x ^ (l - m))) =
        exteriorPower.map k (LinearMap.mulLeft R (x ^ (l - n))) := by
    rw [← exteriorPower.map_comp, hd]
  exact (ModuleCat.ofHom_comp _ _).symm.trans (congrArg ModuleCat.ofHom he)

/-- The inverse system `n ↦ K(xᵢⁿ)` with the diagonal power transitions.

The body is exposed so that its terms are the existing Koszul complexes, and their elements
can be used as exterior-power elements without transport. -/
@[expose] def powerTower : ℕᵒᵖ ⥤ ChainComplex (ModuleCat.{max u v} R) ℕ where
  obj n := koszulComplex (Fintype.linearCombination R (fun i ↦ x i ^ n.unop))
  map f := powerMap x (leOfHom f.unop)
  map_id n := powerMap_refl x n.unop
  map_comp f g := (powerMap_comp x (leOfHom g.unop) (leOfHom f.unop)).symm

@[simp]
theorem powerTower_obj (n : ℕ) :
    (powerTower x).obj (op n) =
      koszulComplex (Fintype.linearCombination R (fun i ↦ x i ^ n)) :=
  (rfl)

@[simp]
theorem powerTower_map {n m : ℕ} (h : n ≤ m) :
    (powerTower x).map (homOfLE h).op = powerMap x h :=
  (rfl)

/-- All power transitions are the identity in degree zero. -/
@[simp]
theorem powerMap_f_zero {n m : ℕ} (h : n ≤ m) :
    (powerMap x h).f 0 = 𝟙 (ModuleCat.of R (⋀[R]^0 (ι → R))) := by
  rw [powerMap_f]
  have he : exteriorPower.map 0 (LinearMap.mulLeft R (x ^ (m - n))) = LinearMap.id := by
    apply LinearMap.ext
    intro z
    apply (exteriorPower.zeroEquiv R (ι → R)).injective
    exact LinearMap.congr_fun (exteriorPower.zeroEquiv_naturality
      (LinearMap.mulLeft R (x ^ (m - n)))) z
  exact (congrArg ModuleCat.ofHom he).trans ModuleCat.ofHom_id

/-- The degree-one transition, under `⋀¹ Rⁱ ≃ Rⁱ`, multiplies coordinate `i` by `xᵢ^(m-n)`. -/
@[simp]
theorem oneEquiv_powerMap {n m : ℕ} (h : n ≤ m) (z : ⋀[R]^1 (ι → R)) (i : ι) :
    exteriorPower.oneEquiv R (ι → R) ((powerMap x h).f 1 z) i =
      x i ^ (m - n) * exteriorPower.oneEquiv R (ι → R) z i := by
  rw [powerMap_f]
  exact congrFun (LinearMap.congr_fun
    (exteriorPower.oneEquiv_naturality (LinearMap.mulLeft R (x ^ (m - n)))) z) i

/-- In positive degree the image of a transition lies in `J • ⊤` whenever all diagonal entries
lie in `J`. This estimate includes degrees above the length of the sequence. -/
theorem powerMap_mem_smul {n m k : ℕ} (h : n ≤ m) (hk : 0 < k) (J : Ideal R)
    (hJ : ∀ i, x i ^ (m - n) ∈ J) (z : ⋀[R]^k (ι → R)) :
    (powerMap x h).f k z ∈ J • (⊤ : Submodule R (⋀[R]^k (ι → R))) := by
  classical
  let : LinearOrder ι := linearOrderOfSTO WellOrderingRel
  let b := Pi.basisFun R ι
  let P : Submodule R (⋀[R]^k (ι → R)) := J • ⊤
  have hle : ⊤ ≤ P.comap (exteriorPower.map k (LinearMap.mulLeft R (x ^ (m - n)))) := by
    rw [← (b.exteriorPower k).span_eq, Submodule.span_le]
    rintro _ ⟨s, rfl⟩
    apply (Submodule.mem_comap).2
    rw [b.map_exteriorPower_of_apply _
      (fun i ↦ x i ^ (m - n)) (fun i ↦ by
        ext j
        by_cases hij : i = j
        · subst j; simp [b, Pi.basisFun_apply, LinearMap.mulLeft_apply]
        · simp [b, Pi.basisFun_apply, LinearMap.mulLeft_apply, hij])]
    have hs : (s : Finset ι).Nonempty := Finset.card_pos.mp (s.2.symm ▸ hk)
    obtain ⟨i, hi⟩ := hs
    exact Submodule.smul_mem_smul (J.prod_mem hi (hJ i)) Submodule.mem_top
  rw [powerMap_f]
  exact hle (Submodule.mem_top (x := z))

end TauCeti.koszulComplex
