/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.HomotopyCofiber
public import TauCeti.LinearAlgebra.ExteriorPower.Prod
public import TauCeti.RingTheory.KoszulComplex.Basic

/-!
# The Koszul complex of `φ` with one element adjoined is a mapping cone

For a linear functional `φ : M → R` and `y : R`, write `K(φ, y)` for the Koszul complex of the
functional `(m, r) ↦ φ(m) + r y` on `M × R`. With `e = (0, 1)`, every element of `⋀ⁿ⁺¹ (M × R)`
is uniquely `a + e ∧ b` with `a ∈ ⋀ⁿ⁺¹ M` and `b ∈ ⋀ⁿ M`, and the Koszul differential is
`d(a + e ∧ b) = (d a + y b) - e ∧ d b`. This is the differential `(b, a) ↦ (-d b, y b + d a)` of
the mapping cone of multiplication by `y` on `K(φ)`, with the sign convention of Mathlib's
`HomologicalComplex.homotopyCofiber`. Hence `K(φ, y) ≅ Cone(y : K(φ) → K(φ))`, and the long exact
homology sequence of the cone relates the homology of `K(φ, y)` to multiplication by `y` on the
homology of `K(φ)`.

The Koszul complex is an `ℕ`-indexed chain complex, so its mapping cone is Mathlib's
`HomologicalComplex.homotopyCofiber`, of which `CochainComplex.mappingCone` is the `ℤ`-indexed
cochain case. The isomorphism is the map out of the cone given by `⋀ inl : K(φ) → K(φ, y)` on the
target summand and by `b ↦ e ∧ b` on the shifted summand; the latter is the null-homotopy
`TauCeti.koszulComplex.smulHomotopy` of multiplication by `φ(e) = y` on `K(φ, y)`. Its inverse
sends `z` to `(⋀ fst (ι_snd z), ⋀ fst z)`, where `ι_snd` is the contraction by the second
coordinate, by the splitting
`ExteriorAlgebra.map_inl_map_fst_add_ι_inr_mul_contractLeft_snd`.

## Main declarations

* `TauCeti.koszulComplex.homotopyCofiberIso`: the isomorphism between the mapping cone of
  multiplication by `y` on `K(φ)` and `K(φ, y)`.
* `TauCeti.koszulComplex.inrX_homotopyCofiberIso_hom_f` and
  `TauCeti.koszulComplex.inlX_homotopyCofiberIso_hom_f`: the isomorphism is `a ↦ a` on the
  summand `⋀ⁿ M` of the cone in degree `n`, and `b ↦ e ∧ b` on the summand `⋀ⁿ M` of the cone in
  degree `n + 1`.
* `TauCeti.koszulComplex.homotopyCofiberIso_inv_f_sndX` and
  `TauCeti.koszulComplex.homotopyCofiberIso_inv_f_fstX`: the components `⋀ fst` and
  `⋀ fst ∘ ι_snd` of the inverse.

## References

* [The Stacks Project, Lemma 15.29.5 (Tag 0626)](https://stacks.math.columbia.edu/tag/0626)
-/

public section

noncomputable section

universe u v

open CategoryTheory HomologicalComplex CliffordAlgebra

namespace TauCeti

variable {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]

namespace koszulComplex

variable (φ : Module.Dual R M) (y : R)

/-- The chain map `K(φ) → K(φ, y)` induced by the inclusion `inl : M → M × R`. -/
private def inlHom :
    koszulComplex φ ⟶ koszulComplex (φ.coprod (LinearMap.toSpanSingleton R R y)) :=
  ChainComplex.ofHom (fun n ↦ ModuleCat.ofHom (exteriorPower.map n (LinearMap.inl R M R)))
    fun n ↦ by
      rw [koszulComplex_d, koszulComplex_d]
      exact ModuleCat.hom_ext (koszulDifferential_comp_map _ (LinearMap.coprod_inl _ _) n)

private theorem inlHom_f (n : ℕ) :
    (inlHom φ y).f n = ModuleCat.ofHom (exteriorPower.map n (LinearMap.inl R M R)) :=
  (rfl)

/-- The null-homotopy `b ↦ e ∧ b` of `K(φ) → K(φ, y)` followed by multiplication by `y`. -/
private def inlHomotopy : Homotopy ((y • 𝟙 (koszulComplex φ)) ≫ inlHom φ y) 0 :=
  (Homotopy.ofEq (by simp)).trans
    (((smulHomotopy _ (LinearMap.inr R M R 1)).compLeft (inlHom φ y)).trans
      (Homotopy.ofEq (Limits.comp_zero)))

private theorem inlHomotopy_hom (n : ℕ) :
    (inlHomotopy φ y).hom n (n + 1) =
      (ModuleCat.ofHom (ExteriorAlgebra.wedgeLeft (LinearMap.inr R M R 1) n ∘ₗ
        exteriorPower.map n (LinearMap.inl R M R)) :
          (koszulComplex φ).X n ⟶
            (koszulComplex (φ.coprod (LinearMap.toSpanSingleton R R y))).X (n + 1)) := by
  simp only [inlHomotopy, Homotopy.trans_hom, Homotopy.ofEq_hom, Homotopy.compLeft_hom,
    Pi.zero_apply, zero_add, add_zero, inlHom_f, smulHomotopy_hom, ModuleCat.ofHom_comp]
  -- The two sides differ only in whether the objects are written as terms of Koszul complexes.
  rfl

/-- The `⋀ M`-component `z ↦ ⋀ fst z` of an element of `K(φ, y)`. -/
private def projFst (n : ℕ) :
    (koszulComplex (φ.coprod (LinearMap.toSpanSingleton R R y))).X n ⟶ (koszulComplex φ).X n :=
  ModuleCat.ofHom (exteriorPower.map n (LinearMap.fst R M R))

/-- The `e`-component `z ↦ ⋀ fst (ι_snd z)` of an element of `K(φ, y)`. -/
private def projSnd (n : ℕ) :
    (koszulComplex (φ.coprod (LinearMap.toSpanSingleton R R y))).X (n + 1) ⟶
      (koszulComplex φ).X n :=
  ModuleCat.ofHom (exteriorPower.map n (LinearMap.fst R M R) ∘ₗ
    koszulDifferential (LinearMap.snd R M R) n)

@[reassoc]
private theorem inlHom_f_projFst (n : ℕ) : (inlHom φ y).f n ≫ projFst φ y n = 𝟙 _ :=
  ModuleCat.hom_ext (exteriorPower.map_fst_comp_map_inl n)

@[reassoc]
private theorem inlHom_f_projSnd (n : ℕ) : (inlHom φ y).f (n + 1) ≫ projSnd φ y n = 0 :=
  ModuleCat.hom_ext (map_fst_koszulDifferential_snd_comp_map_inl n)

@[reassoc]
private theorem inlHomotopy_hom_projFst (n : ℕ) :
    (inlHomotopy φ y).hom n (n + 1) ≫ projFst φ y (n + 1) = 0 := by
  rw [inlHomotopy_hom]
  exact ModuleCat.hom_ext (exteriorPower.map_fst_comp_wedgeLeft (1 : R) n)

@[reassoc]
private theorem inlHomotopy_hom_projSnd (n : ℕ) :
    (inlHomotopy φ y).hom n (n + 1) ≫ projSnd φ y n = 𝟙 _ := by
  rw [inlHomotopy_hom]
  exact ModuleCat.hom_ext (map_fst_koszulDifferential_snd_comp_wedgeLeft n)

private theorem projSnd_inlHomotopy_hom_add (n : ℕ) :
    projSnd φ y n ≫ (inlHomotopy φ y).hom n (n + 1) + projFst φ y (n + 1) ≫ (inlHom φ y).f (n + 1) =
      𝟙 _ := by
  rw [inlHomotopy_hom]
  exact ModuleCat.hom_ext (wedgeLeft_comp_add_map_inl_comp n)

private theorem projFst_inlHom_f_zero : projFst φ y 0 ≫ (inlHom φ y).f 0 = 𝟙 _ :=
  ModuleCat.hom_ext exteriorPower.map_inl_comp_map_fst_zero

/-- The inverse of the map out of the cone in each degree: `z ↦ (⋀ fst (ι_snd z), ⋀ fst z)`. -/
private def coneInvX : (n : ℕ) →
    (koszulComplex (φ.coprod (LinearMap.toSpanSingleton R R y))).X n ⟶
      (homotopyCofiber (y • 𝟙 (koszulComplex φ))).X n
  | 0 => projFst φ y 0 ≫ homotopyCofiber.inrX (y • 𝟙 (koszulComplex φ)) 0
  | n + 1 =>
    projSnd φ y n ≫
        homotopyCofiber.inlX (y • 𝟙 (koszulComplex φ)) n (n + 1) (ComplexShape.down_mk _ _ rfl) +
      projFst φ y (n + 1) ≫ homotopyCofiber.inrX (y • 𝟙 (koszulComplex φ)) (n + 1)

private theorem not_rel_zero : ¬ (ComplexShape.down ℕ).Rel 0 ((ComplexShape.down ℕ).next 0) :=
  fun h ↦ Nat.succ_ne_zero _ h

private theorem desc_f_coneInvX (n : ℕ) :
    (homotopyCofiber.desc _ (inlHom φ y) (inlHomotopy φ y)).f n ≫ coneInvX φ y n = 𝟙 _ := by
  cases n with
  | zero =>
    refine homotopyCofiber.ext_from_X' (y • 𝟙 (koszulComplex φ)) 0 not_rel_zero ?_
    simp [coneInvX, inlHom_f_projFst_assoc]
  | succ n =>
    refine homotopyCofiber.ext_from_X (y • 𝟙 (koszulComplex φ)) n (n + 1)
      (ComplexShape.down_mk _ _ rfl) ?_ ?_
    · simp [coneInvX, inlHomotopy_hom_projSnd_assoc, inlHomotopy_hom_projFst_assoc]
    · simp [coneInvX, inlHom_f_projSnd_assoc, inlHom_f_projFst_assoc]

private theorem coneInvX_desc_f (n : ℕ) :
    coneInvX φ y n ≫ (homotopyCofiber.desc _ (inlHom φ y) (inlHomotopy φ y)).f n = 𝟙 _ := by
  cases n with
  | zero => simpa [coneInvX] using projFst_inlHom_f_zero φ y
  | succ n => simpa [coneInvX] using projSnd_inlHomotopy_hom_add φ y n

/-- **The Koszul complex of `φ` with `y` adjoined is the mapping cone of `y` on `K(φ)`**: for the
functional `(m, r) ↦ φ(m) + r y` on `M × R`, its Koszul complex `K(φ, y)` is isomorphic to the
mapping cone of multiplication by `y` on `K(φ)`. In degree `n + 1`, the cone is
`⋀ⁿ M ⊕ ⋀ⁿ⁺¹ M`, and `(b, a) ↦ a + e ∧ b` with `e = (0, 1)`; see
`inlX_homotopyCofiberIso_hom_f` and `inrX_homotopyCofiberIso_hom_f`. -/
def homotopyCofiberIso :
    homotopyCofiber (y • 𝟙 (koszulComplex φ)) ≅
      koszulComplex (φ.coprod (LinearMap.toSpanSingleton R R y)) :=
  Hom.isoOfComponents
    (fun n ↦ ⟨(homotopyCofiber.desc _ (inlHom φ y) (inlHomotopy φ y)).f n, coneInvX φ y n,
      desc_f_coneInvX φ y n, coneInvX_desc_f φ y n⟩)
    fun i j _ ↦ (homotopyCofiber.desc _ (inlHom φ y) (inlHomotopy φ y)).comm i j

/-- On the summand `⋀ⁿ M` of the mapping cone in degree `n`, the isomorphism with `K(φ, y)` is
`⋀ inl`. -/
@[reassoc (attr := simp)]
theorem inrX_homotopyCofiberIso_hom_f (n : ℕ) :
    homotopyCofiber.inrX (y • 𝟙 (koszulComplex φ)) n ≫ (homotopyCofiberIso φ y).hom.f n =
      ModuleCat.ofHom (exteriorPower.map n (LinearMap.inl R M R)) :=
  homotopyCofiber.inrX_desc_f _ _ _ n

/-- On the summand `⋀ⁿ M` of the mapping cone in degree `n + 1`, the isomorphism with `K(φ, y)`
is `b ↦ e ∧ b` with `e = (0, 1)`. -/
@[reassoc (attr := simp)]
theorem inlX_homotopyCofiberIso_hom_f (n : ℕ) :
    homotopyCofiber.inlX (y • 𝟙 (koszulComplex φ)) n (n + 1) (ComplexShape.down_mk _ _ rfl) ≫
        (homotopyCofiberIso φ y).hom.f (n + 1) =
      ModuleCat.ofHom (ExteriorAlgebra.wedgeLeft (LinearMap.inr R M R 1) n ∘ₗ
        exteriorPower.map n (LinearMap.inl R M R)) :=
  (homotopyCofiber.inlX_desc_f _ _ _ n (n + 1) (ComplexShape.down_mk _ _ rfl)).trans
    (inlHomotopy_hom φ y n)

/-- The second component of the inverse isomorphism `K(φ, y) → Cone(y)` is `z ↦ ⋀ fst z`. -/
@[reassoc (attr := simp)]
theorem homotopyCofiberIso_inv_f_sndX (n : ℕ) :
    (homotopyCofiberIso φ y).inv.f n ≫ homotopyCofiber.sndX (y • 𝟙 (koszulComplex φ)) n =
      ModuleCat.ofHom (exteriorPower.map n (LinearMap.fst R M R)) := by
  cases n <;> simpa [homotopyCofiberIso, coneInvX] using projFst.eq_1 φ y _

/-- The first component of the inverse isomorphism `K(φ, y) → Cone(y)` in degree `n + 1` is
`z ↦ ⋀ fst (ι_snd z)`, with `ι_snd` the contraction by the second coordinate. -/
@[reassoc (attr := simp)]
theorem homotopyCofiberIso_inv_f_fstX (n : ℕ) :
    (homotopyCofiberIso φ y).inv.f (n + 1) ≫
        homotopyCofiber.fstX (y • 𝟙 (koszulComplex φ)) (n + 1) n (ComplexShape.down_mk _ _ rfl) =
      ModuleCat.ofHom (exteriorPower.map n (LinearMap.fst R M R) ∘ₗ
        koszulDifferential (LinearMap.snd R M R) n) := by
  simpa [homotopyCofiberIso, coneInvX] using projSnd.eq_1 φ y n

end koszulComplex

end TauCeti
