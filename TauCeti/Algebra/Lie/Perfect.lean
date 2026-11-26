/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.Solvable

/-!
# Perfect Lie algebras and uniqueness of lifts from them

Two morphisms from a perfect Lie algebra into a central extension are equal if their
projections are equal. Their difference takes values in the central kernel, so they agree
on brackets, which span the source. This gives the uniqueness part of universal central
extension constructions without imposing any condition on the map of kernels.

A surjective Lie homomorphism carries the derived series onto the derived series
(`LieIdeal.derivedSeries_map_eq`), so the image of a perfect Lie algebra is perfect.

A Lie algebra spanned by its centre and its derived ideal, `L = 𝔷(L) + ⁅L, L⁆`, has a perfect
derived ideal: central elements contribute nothing to brackets.

## Main results

* `LieHom.eq_of_comp_eq_of_ker_le_center`: morphisms from a perfect Lie algebra into a central
  extension are determined by their projections.
* `LieHom.derivedSeries_eq_top_of_surjective`: a term of the derived series that is everything
  stays everything along a surjective Lie homomorphism; in particular perfectness passes to
  quotients and isomorphic Lie algebras.
* `TauCeti.exists_mem_center_add_mem_derivedSeries_of_sup_eq_top` and
  `TauCeti.lie_derivedSeries_derivedSeries_eq_self_of_sup_eq_top`: when `L = 𝔷(L) + ⁅L, L⁆`, every
  element splits as a central element plus a derived one, and the derived ideal is perfect.
* `LieHom.derivedSeries_one_eq_top_of_range_eq_of_sup_eq_top`: when `L = 𝔷(L) + ⁅L, L⁆`, a Lie
  algebra embedded onto the derived ideal is perfect.
-/

public section

namespace TauCeti

open LieAlgebra

variable {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]

/-- Every element of a Lie algebra spanned by its centre and its derived ideal is a central element
plus an element of the derived ideal. -/
theorem exists_mem_center_add_mem_derivedSeries_of_sup_eq_top
    (h : center R L ⊔ derivedSeries R L 1 = ⊤) (x : L) :
    ∃ z ∈ center R L, ∃ d ∈ derivedSeries R L 1, z + d = x :=
  (LieSubmodule.mem_sup _ _ x).mp (h ▸ LieSubmodule.mem_top x)

/-- **The derived ideal is perfect when it spans the Lie algebra together with the centre**:
`⁅⁅L, L⁆, ⁅L, L⁆⁆ = ⁅L, L⁆`. A central element contributes nothing to a bracket, so writing both
arguments of a generating bracket of `⁅L, L⁆` as a central element plus an element of `⁅L, L⁆`
leaves only the brackets of the derived ideal with itself. -/
theorem lie_derivedSeries_derivedSeries_eq_self_of_sup_eq_top
    (h : center R L ⊔ derivedSeries R L 1 = ⊤) :
    ⁅derivedSeries R L 1, derivedSeries R L 1⁆ = derivedSeries R L 1 := by
  refine le_antisymm (LieSubmodule.lie_le_right _ _) ?_
  have hDtop : derivedSeries R L 1 = ⁅(⊤ : LieIdeal R L), (⊤ : LieIdeal R L)⁆ := by
    rw [derivedSeries_def, derivedSeriesOfIdeal_succ, derivedSeriesOfIdeal_zero]
  rw [hDtop]
  refine (LieSubmodule.lie_le_iff _ _ _).2 fun y _ z _ ↦ ?_
  obtain ⟨zy, hzy, dy, hdy, rfl⟩ := exists_mem_center_add_mem_derivedSeries_of_sup_eq_top h y
  obtain ⟨zz, hzz, dz, hdz, rfl⟩ := exists_mem_center_add_mem_derivedSeries_of_sup_eq_top h z
  have hzy0 : ∀ w : L, ⁅zy, w⁆ = 0 := fun w ↦ by
    rw [← lie_skew, (LieModule.mem_maxTrivSubmodule R L L zy).1 hzy w, neg_zero]
  have hzz0 : ∀ w : L, ⁅w, zz⁆ = 0 := (LieModule.mem_maxTrivSubmodule R L L zz).1 hzz
  rw [add_lie, hzy0, lie_add, hzz0, zero_add, zero_add]
  exact LieSubmodule.lie_mem_lie hdy hdz

end TauCeti

namespace LieHom

variable {R L E Q : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
  [LieRing E] [LieAlgebra R E] [LieRing Q] [LieAlgebra R Q]

/-- Morphisms from a perfect Lie algebra into a Lie algebra with a central projection kernel
are determined by their composites with that projection. Surjectivity of the projection is
not required. -/
theorem eq_of_comp_eq_of_ker_le_center (f g : L →ₗ⁅R⁆ E) (p : E →ₗ⁅R⁆ Q)
    (hL : LieAlgebra.derivedSeries R L 1 = ⊤)
    (hp : p.ker ≤ LieAlgebra.center R E) (h : p.comp f = p.comp g) : f = g := by
  have hd (x : L) : f x - g x ∈ LieAlgebra.center R E := by
    apply hp
    simp only [LieHom.mem_ker, map_sub, sub_eq_zero]
    exact DFunLike.congr_fun h x
  have hb (x y : L) : f ⁅x, y⁆ = g ⁅x, y⁆ := by
    have hx := (LieModule.mem_maxTrivSubmodule R E E _).mp (hd x) (f y)
    have hy := (LieModule.mem_maxTrivSubmodule R E E _).mp (hd y) (g x)
    rw [lie_sub, sub_eq_zero] at hx hy
    have hx' := congrArg Neg.neg hx
    simp only [lie_skew] at hx'
    simpa only [map_lie] using hx'.trans hy
  apply LieHom.ext
  intro x
  have hx : x ∈ Submodule.span R {⁅a, b⁆ | (a : L) (b : L)} := by
    rw [← LieAlgebra.coe_derivedSeries_one_eq, hL]
    simp
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, b, rfl⟩ := hx
    exact hb a b
  | zero => simp
  | add x y _ _ hx hy => simp [hx, hy]
  | smul r x _ hx => simp [hx]

/-- If the `k`-th term of the derived series of `L` is `⊤`, so is that of the target of a
surjective Lie homomorphism `f : L →ₗ⁅R⁆ Q`. For `k = 1`: the image of a perfect Lie algebra is
perfect. -/
theorem derivedSeries_eq_top_of_surjective (f : L →ₗ⁅R⁆ Q) (hf : Function.Surjective f) {k : ℕ}
    (h : LieAlgebra.derivedSeries R L k = ⊤) : LieAlgebra.derivedSeries R Q k = ⊤ := by
  rw [← LieIdeal.derivedSeries_map_eq k hf, h, ← f.idealRange_eq_map,
    f.idealRange_eq_top_of_surjective hf]

section Embedding

open LieAlgebra

variable {L' : Type*} [LieRing L'] [LieAlgebra R L']

/-- **A Lie algebra embedded onto the derived ideal is perfect when the centre and the derived
ideal span.** If `L = 𝔷(L) + ⁅L, L⁆` and `f : L' → L` is injective with range `⁅L, L⁆`, then
`⁅L', L'⁆ = L'`: the derived ideal `⁅L, L⁆` is perfect
(`TauCeti.lie_derivedSeries_derivedSeries_eq_self_of_sup_eq_top`), and `f` identifies `L'` with
it. -/
theorem derivedSeries_one_eq_top_of_range_eq_of_sup_eq_top (f : L' →ₗ⁅R⁆ L)
    (hf : Function.Injective f)
    (hr : LinearMap.range f.toLinearMap = (derivedSeries R L 1).toSubmodule)
    (h : center R L ⊔ derivedSeries R L 1 = ⊤) : derivedSeries R L' 1 = ⊤ := by
  have hD : derivedSeries R (derivedSeries R L 1) 1 = ⊤ := by
    rw [LieIdeal.derivedSeries_eq_derivedSeriesOfIdeal_comap, derivedSeriesOfIdeal_succ,
      derivedSeriesOfIdeal_zero,
      TauCeti.lie_derivedSeries_derivedSeries_eq_self_of_sup_eq_top h,
      LieIdeal.comap_incl_self]
  have hs : (f.range : Set L) = (derivedSeries R L 1).toLieSubalgebra := by
    rw [← LieSubalgebra.coe_toSubmodule, f.range_toSubmodule, hr,
      ← LieIdeal.toLieSubalgebra_toSubmodule, LieSubalgebra.coe_toSubmodule]
  let e : L' ≃ₗ⁅R⁆ (derivedSeries R L 1).toLieSubalgebra :=
    (LieEquiv.ofInjective f hf).trans (LieEquiv.ofEq _ _ hs)
  exact derivedSeries_eq_top_of_surjective e.symm.toLieHom e.symm.surjective hD

end Embedding

end LieHom
