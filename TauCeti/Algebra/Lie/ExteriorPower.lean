/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.LinearAlgebra.ExteriorPower.WedgePairing
public import Mathlib.LinearAlgebra.Trace
public import TauCeti.LinearAlgebra.ExteriorAlgebra.Derivation.OfEnd
import TauCeti.LinearAlgebra.Alternating.Basic
import TauCeti.LinearAlgebra.ExteriorPower.WedgePairing
import TauCeti.LinearAlgebra.Trace.Basic

/-!
# Lie actions on exterior powers

An endomorphism of a module acts infinitesimally on an exterior power by applying the
endomorphism to one factor at a time. This construction is linear in the endomorphism and carries
commutators to commutators, hence defines a Lie algebra representation. It is the restriction to
`⋀[K]^d V` of the derivation `ExteriorAlgebra.derivationOfEnd K V f` of the exterior algebra, so it
is a derivation of the wedge product. In degree `Module.finrank K V` of a free module it is
multiplication by the trace of the endomorphism: the infinitesimal form of the action of `⋀ⁿ f` by
`det f`. For a finite free module this degree is the top exterior power; for an infinite free
module it is degree zero and the trace is zero.

## Main definitions

* `exteriorPower.lieMap`: the natural Lie action of `Module.End K V` on `⋀[K]^d V`.

## Main results

* `ExteriorAlgebra.derivationOfEnd_apply_coe`: on `⋀[K]^d V` the derivation of the exterior algebra
  induced by `f` is `exteriorPower.lieMap d f`.
* `exteriorPower.lieMap_apply_ιMulti`: the action on a decomposable wedge is the sum of the terms
  obtained by applying the endomorphism to one factor.
* `exteriorPower.lieMap_two_apply_ιMulti`: on two-vectors this is the derivation rule
  `f (u ∧ w) = f u ∧ w + u ∧ f w`.
* `exteriorPower.lieMap_wedge`: the Leibniz rule `f (x ∧ y) = f x ∧ y + x ∧ f y`.
* `exteriorPower.lieMap_finrank_apply`: in degree `Module.finrank K V` (the top exterior power
  when `V` is finite), `f` acts by `trace f`.
* `exteriorPower.wedgePairing_lieMap_add_wedgePairing_lieMap`: consequently, for a pairing of
  complementary exterior powers, `⟨f x, y⟩ + ⟨x, f y⟩ = trace f * ⟨x, y⟩`.
-/

public section

namespace exteriorPower

attribute [local instance 100] LieRing.ofAssociativeRing

variable {K V : Type*} [CommRing K] [AddCommGroup V] [Module K V]

/-- The infinitesimal action of endomorphisms on an exterior power: the restriction of the
derivation `ExteriorAlgebra.derivationOfEnd K V f` of the exterior algebra to `⋀[K]^d V`. -/
noncomputable def lieMap (d : ℕ) :
    Module.End K V →ₗ⁅K⁆ Module.End K (⋀[K]^d V) where
  toFun f := (ExteriorAlgebra.derivationOfEnd K V f : Module.End K (ExteriorAlgebra K V)).restrict
    fun _ ↦ ExteriorAlgebra.derivationOfEnd_mem_exteriorPower f
  map_add' f g := LinearMap.ext fun x ↦ Subtype.ext <| by simp
  map_smul' r f := LinearMap.ext fun x ↦ Subtype.ext <| by simp
  map_lie' {f g} := LinearMap.ext fun x ↦ Subtype.ext <| by
    simp only [LinearMap.coe_restrict_apply]
    rw [LieHom.map_lie]
    simp [Ring.lie_def]

/-- **On an exterior power, the derivation induced by `f` is the infinitesimal action**
`exteriorPower.lieMap d f`. -/
theorem _root_.ExteriorAlgebra.derivationOfEnd_apply_coe (f : Module.End K V) {d : ℕ}
    (x : ⋀[K]^d V) :
    (ExteriorAlgebra.derivationOfEnd K V f : Module.End K (ExteriorAlgebra K V)) x =
      lieMap d f x := by
  rfl

/-- An endomorphism acts on a decomposable wedge by acting on one factor at a time. -/
@[simp]
theorem lieMap_apply_ιMulti (d : ℕ) (f : Module.End K V) (v : Fin d → V) :
    lieMap d f (ιMulti K d v) =
      ∑ i : Fin d, ιMulti K d (Function.update v i (f (v i))) :=
  Subtype.ext <| by
    simp [← ExteriorAlgebra.derivationOfEnd_apply_coe, ExteriorAlgebra.derivationOfEnd_ιMulti]

/-- On two-vectors an endomorphism acts by the derivation rule `f (u ∧ w) = f u ∧ w + u ∧ f w`. -/
theorem lieMap_two_apply_ιMulti (f : Module.End K V) (u w : V) :
    lieMap 2 f (ιMulti K 2 ![u, w]) = ιMulti K 2 ![f u, w] + ιMulti K 2 ![u, f w] := by
  rw [lieMap_apply_ιMulti, Fin.sum_univ_two]
  congr 2 <;> ext i <;> fin_cases i <;> rfl

/-- **The Leibniz rule**: an endomorphism acts on a wedge product as a derivation,
`f (x ∧ y) = f x ∧ y + x ∧ f y`. -/
theorem lieMap_wedge (f : Module.End K V) {k l : ℕ} (x : ⋀[K]^k V) (y : ⋀[K]^l V) :
    lieMap (k + l) f (wedge K V k l x y) =
      wedge K V k l (lieMap k f x) y + wedge K V k l x (lieMap l f y) :=
  Subtype.ext <| by
    simp only [← ExteriorAlgebra.derivationOfEnd_apply_coe, coe_wedge, Submodule.coe_add,
      TauCeti.derivationLieAlgebra.leibniz]

/-- An endomorphism of a free module acts in degree `Module.finrank K V` by multiplication by its
trace: the infinitesimal form of `LinearMap.map_exteriorPower_finrank_eq_det_smul`. For a finite
module this degree is the top exterior power; for an infinite free module it is degree zero, where
the action and the trace both vanish. -/
@[simp]
theorem lieMap_finrank_apply [Module.Free K V]
    (f : Module.End K V) (x : ⋀[K]^(Module.finrank K V) V) :
    lieMap _ f x = LinearMap.trace K V f • x := by
  classical
  cases subsingleton_or_nontrivial K
  · have := Module.subsingleton K (⋀[K]^(Module.finrank K V) V)
    exact Subsingleton.elim _ _
  by_cases hfin : Module.Finite K V
  swap
  · have hzero : ∀ {d : ℕ}, d = 0 → lieMap (K := K) (V := V) d f = 0 := by
      rintro d rfl
      exact linearMap_ext (AlternatingMap.ext fun v ↦ by simp)
    have htr : LinearMap.trace K V f = 0 := by
      simp [TauCeti.LinearMap.trace_eq_zero_of_not_finite hfin]
    rw [hzero (Module.finrank_of_not_finite hfin), htr]
    simp
  let b := Module.finBasis K V
  -- Every element of the basis of the top exterior power is the wedge of `b`, on which `f`
  -- contributes the diagonal coefficient `b.repr (f (b i)) i` from the `i`-th factor.
  have htop : lieMap _ f (ιMulti K _ b) = LinearMap.trace K V f • ιMulti K _ b := by
    have hterm (i : Fin (Module.finrank K V)) : ιMulti K _ (Function.update b i (f (b i))) =
        b.repr (f (b i)) i • ιMulti K _ b := by
      conv_lhs => rw [← b.sum_repr (f (b i))]
      exact (ιMulti K _).map_update_sum_smul b (Finset.mem_univ i) _
    rw [lieMap_apply_ιMulti, Finset.sum_congr rfl fun i _ ↦ hterm i, ← Finset.sum_smul,
      LinearMap.trace_eq_matrix_trace K b, Matrix.trace]
    simp [LinearMap.toMatrix_apply]
  have hb : ∀ s, b.exteriorPower (Module.finrank K V) s = ιMulti K _ b := fun s ↦ by
    rw [Module.Basis.topVector_eq_exteriorPower, b.topVector_eq_ιMulti rfl, finCongr_refl,
      Equiv.coe_refl, Function.comp_id]
  have : lieMap (Module.finrank K V) f = LinearMap.trace K V f • LinearMap.id :=
    (b.exteriorPower _).ext fun s ↦ by rw [hb, LinearMap.smul_apply, LinearMap.id_apply, htop]
  simpa using LinearMap.congr_fun this x

/-- **Endomorphisms are infinitesimally conformal for wedge pairings**: for every trivialization
`vol` of the exterior power in degree `Module.finrank K V` (the top exterior power when `V` is
finite), `vol (f x ∧ y) + vol (x ∧ f y) = trace f * vol (x ∧ y)`. -/
theorem wedgePairing_lieMap_add_wedgePairing_lieMap [Module.Free K V]
    (vol : ⋀[K]^(Module.finrank K V) V ≃ₗ[K] K) {k l : ℕ}
    (hkl : k + l = Module.finrank K V) (f : Module.End K V) (x : ⋀[K]^k V) (y : ⋀[K]^l V) :
    wedgePairing vol hkl (lieMap k f x) y + wedgePairing vol hkl x (lieMap l f y) =
      LinearMap.trace K V f * wedgePairing vol hkl x y := by
  -- Read the wedge pairing in the top degree, where `f` acts by its trace.
  have htop : lieMap (Module.finrank K V) f = LinearMap.trace K V f • LinearMap.id :=
    LinearMap.ext (lieMap_finrank_apply f)
  rw [← hkl] at htop
  simp only [LinearMap.compr₂_apply]
  rw [← map_add, ← lieMap_wedge, htop, LinearMap.smul_apply, LinearMap.id_apply, map_smul,
    smul_eq_mul]

end exteriorPower
