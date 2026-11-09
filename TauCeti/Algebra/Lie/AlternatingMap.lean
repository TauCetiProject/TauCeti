/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.OfAssociative
public import TauCeti.LinearAlgebra.Alternating.Derivation

/-!
# The Lie module of alternating maps

Let `M` and `N` be modules over a Lie algebra `L`. Then `L` acts on the alternating maps
`ω : M [⋀^ι]→ₗ[R] N` by
`⁅x, ω⁆ v = ⁅x, ω v⁆ - ∑ i, ω (update v i ⁅x, v i⁆)`,
extending Mathlib's action `LinearMap.instLieRingModule` on linear maps. The first term is the
action on the values and the second is the derivation induced by the action on the arguments
(`LinearMap.alternatingDerivation`). For `M = L` acting on itself by the adjoint action, these are
the cochains of the Chevalley–Eilenberg complex of `L` with coefficients in `N`, and `⁅x, ω⁆` is
the Lie derivative of `ω` along `x`.

Inserting a first argument intertwines the action up to the action on that argument
(`AlternatingMap.curryLeft_lie`); this is the identity `[L_x, ι_y] = ι_{[x, y]}` between Lie
derivatives and interior products.

## References

* C. Chevalley and S. Eilenberg, *Cohomology theory of Lie groups and Lie algebras*,
  Trans. Amer. Math. Soc. 63 (1948), 85–124.
-/

public section

open Function

namespace AlternatingMap

variable {R L M N ι : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
  [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]
  [AddCommGroup N] [Module R N] [LieRingModule L N] [LieModule R L N]
  [Fintype ι] [DecidableEq ι]

/-- A Lie algebra acting on `M` and `N` acts on alternating maps from `M` to `N`, on the values
and, as a derivation, on the arguments. -/
instance instBracket : Bracket L (M [⋀^ι]→ₗ[R] N) where
  bracket x ω := LinearMap.compAlternatingMapₗ R (LieModule.toEnd R L N x) ω -
    (LieModule.toEnd R L M x).alternatingDerivation ω

/-- The action splits into the action on values and the derivation on arguments. -/
theorem lie_def (x : L) (ω : M [⋀^ι]→ₗ[R] N) :
    ⁅x, ω⁆ = LinearMap.compAlternatingMapₗ R (LieModule.toEnd R L N x) ω -
      (LieModule.toEnd R L M x).alternatingDerivation ω :=
  (rfl)

/-- The value of `⁅x, ω⁆`: the action on the value of `ω`, minus the values of `ω` with `x`
acting on one argument at a time. -/
@[simp]
theorem lie_apply (x : L) (ω : M [⋀^ι]→ₗ[R] N) (v : ι → M) :
    ⁅x, ω⁆ v = ⁅x, ω v⁆ - ∑ i, ω (update v i ⁅x, v i⁆) := by
  simp [lie_def, LinearMap.alternatingDerivation_apply]

/-- The action on alternating maps is a Lie ring module: the actions on values commute with the
derivations, and both are representations. -/
instance instLieRingModule : LieRingModule L (M [⋀^ι]→ₗ[R] N) where
  add_lie x y ω := by
    simp only [lie_def, map_add, LinearMap.compAlternatingMapₗ_apply,
      LinearMap.add_compAlternatingMap, LinearMap.add_apply, LinearMap.alternatingDerivation_add]
    abel
  lie_add x ω ω' := by
    simp only [lie_def, map_add]
    abel
  leibniz_lie x y ω := by
    set X := LieModule.toEnd R L M x
    set Y := LieModule.toEnd R L M y
    set ρ := fun a : L ↦ LinearMap.compAlternatingMapₗ (ι := ι) (M := M) R (LieModule.toEnd R L N a)
    -- The actions on values commute with the derivations, so only the commutators of the actions
    -- on values and of the derivations remain.
    have hcomm (a : L) (f : M →ₗ[R] M) (ω : M [⋀^ι]→ₗ[R] N) :
        ρ a (f.alternatingDerivation ω) = f.alternatingDerivation (ρ a ω) :=
      (f.alternatingDerivation_compAlternatingMap _ ω).symm
    have hval : ρ ⁅x, y⁆ ω = ρ x (ρ y ω) - ρ y (ρ x ω) := by
      ext v
      simp [ρ]
    have hXY : LieModule.toEnd R L M ⁅x, y⁆ = X ∘ₗ Y - Y ∘ₗ X := by
      ext m
      simp [X, Y]
    have hder := X.alternatingDerivation_alternatingDerivation_sub Y ω
    rw [sub_eq_iff_eq_add] at hder
    simp only [lie_def, map_sub, LinearMap.sub_apply, hXY, LinearMap.alternatingDerivation_sub]
    rw [hval, hcomm, hcomm, hder]
    abel

/-- The action on alternating maps is `R`-bilinear. -/
instance instLieModule : LieModule R L (M [⋀^ι]→ₗ[R] N) where
  smul_lie t x ω := by
    ext v
    simp [Finset.smul_sum, smul_sub]
  lie_smul t x ω := by
    ext v
    simp [Finset.smul_sum, smul_sub]

/-- Inserting `y` as the first argument of `⁅x, ω⁆` is the action of `x` on `ω.curryLeft y`,
corrected by inserting `⁅x, y⁆` instead. -/
theorem curryLeft_lie {n : ℕ} (x : L) (ω : M [⋀^Fin (n + 1)]→ₗ[R] N) (y : M) :
    ⁅x, ω⁆.curryLeft y = ⁅x, ω.curryLeft y⁆ - ω.curryLeft ⁅x, y⁆ := by
  ext v
  simp [Fin.sum_univ_succ, Matrix.vecCons, ← Fin.cons_update, Fin.update_cons_zero]
  abel

end AlternatingMap
