/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Connection.Right.Grassmann
public import TauCeti.RingTheory.CyclicCohomology.Derivation
public import TauCeti.RingTheory.CyclicCohomology.Matrix
public import TauCeti.LinearAlgebra.Matrix.ToLin
import TauCeti.Algebra.BigOperators.Fin
import TauCeti.LinearAlgebra.End.Idempotent

/-!
# Traces of curvature and the cyclic two-cocycle of two derivations

Let `τ : A →+ M` be a trace on a ring `A`, so `τ (x * y) = τ (y * x)`. On the free right
module `ι → A`, with `ι` finite, a right-module endomorphism `T` is left multiplication by the
matrix with entries `T (Pi.single j 1) i`, and `τ` composed with the matrix trace gives the
additive map `TauCeti.piEndTrace τ`. On a direct summand, the range of an idempotent
endomorphism `p`, the trace `TauCeti.rangeEndTrace τ p` of an endomorphism `S` is the trace of
`S` extended by zero on the kernel of `p`. Both vanish on commutators.

Let `δ₁, δ₂` be commuting derivations of a `k`-algebra `A` with `τ ∘ δⱼ = 0`. Integration by
parts says that the trace of the derivative `[∇, S]` of an endomorphism along any connection `∇`
on the range of `p` vanishes. With the change-of-connection formula
`TauCeti.RightConnection.curvature_eq_curvature_add` this shows that the trace of the curvature
`[∇₁, ∇₂]` of connections along `δ₁` and `δ₂` on the range of `p` does not depend on the
connections. For the Grassmann connection of an idempotent matrix `e`, the curvature acts on the
range of `e` as `e (δ₁e δ₂e - δ₂e δ₁e)`, so the curvature trace is the value at `(e, e, e)` of
the matrix extension `φ#Tr` of the cyclic two-cocycle
`φ (a₀, a₁, a₂) = τ (a₀ (δ₁a₁ δ₂a₂ - δ₂a₁ δ₁a₂))` of `TauCeti.traceDerivationPairCochain`, for
`k`-linear `τ`. This is Connes' expression of the Chern number `⟨[e], [φ]⟩ = (φ#Tr)(e, e, e)` of
a finite projective module through the curvature of any connection on it.

## Main definitions

* `TauCeti.piEndTrace τ`: the `τ`-trace `∑ᵢ τ (T (Pi.single i 1) i)` of a right-module
  endomorphism `T` of `ι → A`.
* `TauCeti.rangeEndTrace τ p`: the `τ`-trace of a right-module endomorphism of the range of
  `p`.

## Main results

* `TauCeti.piEndTrace_mul_comm`, `TauCeti.rangeEndTrace_mul_comm`: both traces vanish on
  commutators.
* `TauCeti.rangeEndTrace_derivativeEnd_eq_zero`: the trace of the derivative of an endomorphism
  along a connection vanishes.
* `TauCeti.rangeEndTrace_curvature_eq`: the trace of the curvature does not depend on the
  connections.
* `TauCeti.rangeEndTrace_curvature_eq_matrixCochainExtension`: the trace of the curvature of
  any connections on the range of an idempotent matrix `e` is `(φ#Tr)(e, e, e)`.

## References

* A. Connes, *C\*-algèbres et géométrie différentielle*, C. R. Acad. Sci. Paris Sér. A-B 290
  (1980), A599–A604.
* A. Connes, *Noncommutative Geometry*, Academic Press, 1994, Chapter III, §3, and Chapter IV,
  §6.
-/

public section

namespace TauCeti

open RightConnection

variable {k A M : Type*} [CommRing k] [Ring A] [Algebra k A] [AddCommGroup M] {ι : Type*}

/-! ### The trace on the free right module -/

section Pi

variable [Fintype ι] [DecidableEq ι] (τ : A →+ M)

/-- The `τ`-trace `∑ᵢ τ (T (Pi.single i 1) i)` of a right-module endomorphism `T` of the free
right module `ι → A`: `τ` applied to the trace of the matrix of `T`. -/
def piEndTrace : ((ι → A) →ₗ[Aᵐᵒᵖ] (ι → A)) →+ M where
  toFun T := ∑ i, τ (T (Pi.single i 1) i)
  map_zero' := by simp
  map_add' T S := by simp [Finset.sum_add_distrib]

theorem piEndTrace_apply (T : (ι → A) →ₗ[Aᵐᵒᵖ] (ι → A)) :
    piEndTrace τ T = ∑ i, τ (T (Pi.single i 1) i) :=
  (rfl)

variable {τ}

/-- The `τ`-trace vanishes on commutators of endomorphisms of `ι → A`. -/
theorem piEndTrace_mul_comm (hτ : ∀ x y, τ (x * y) = τ (y * x))
    (T S : (ι → A) →ₗ[Aᵐᵒᵖ] (ι → A)) :
    piEndTrace τ (T * S) = piEndTrace τ (S * T) := by
  simp only [piEndTrace_apply, mul_apply_eq_comp, T.apply_eq_sum_apply_single_one_mul (S _),
    S.apply_eq_sum_apply_single_one_mul (T _), map_sum]
  rw [Finset.sum_comm]
  exact Fintype.sum_congr _ _ fun i ↦ Fintype.sum_congr _ _ fun j ↦ hτ _ _

/-- On left multiplication by a matrix, the `τ`-trace is `τ` of the matrix trace. -/
@[simp]
theorem piEndTrace_mulVecBilin (N : Matrix ι ι A) :
    piEndTrace τ (Matrix.mulVecBilin A Aᵐᵒᵖ N) = τ N.trace := by
  simp [piEndTrace_apply, Matrix.trace, map_sum]

/-- Integration by parts on `ι → A`: if `τ ∘ D = 0`, the trace of the derivative of an
endomorphism along the coordinate connection vanishes. -/
theorem piEndTrace_derivativeEnd_coordinate_eq_zero {D : derivationLieAlgebra k A}
    (hD : ∀ x, τ ((D : Module.End k A) x) = 0) (T : (ι → A) →ₗ[Aᵐᵒᵖ] (ι → A)) :
    piEndTrace τ (derivativeEnd (coordinate D ι) T) = 0 := by
  have h (i : ι) : coordinate D ι (Pi.single i 1) = 0 := by
    ext l
    by_cases hl : l = i
    · subst hl
      simp [derivationLieAlgebra.apply_one_eq_zero]
    · simp [Pi.single_eq_of_ne hl]
  simp [piEndTrace_apply, h, hD]

omit [DecidableEq ι] in
/-- The derivative of left multiplication by a matrix along the coordinate connection is left
multiplication by the entrywise derivative of the matrix. -/
theorem derivativeEnd_coordinate_mulVecBilin (D : derivationLieAlgebra k A) (N : Matrix ι ι A) :
    derivativeEnd (coordinate D ι) (Matrix.mulVecBilin A Aᵐᵒᵖ N) =
      Matrix.mulVecBilin A Aᵐᵒᵖ (N.map (D : Module.End k A)) := by
  refine LinearMap.ext fun x ↦ funext fun i ↦ ?_
  simp [Matrix.mulVec, dotProduct, map_sum, derivationLieAlgebra.leibniz, Finset.sum_add_distrib]

end Pi

/-! ### The trace on a direct summand -/

section Range

variable (τ : A →+ M) (p : (ι → A) →ₗ[Aᵐᵒᵖ] (ι → A))

/-- An endomorphism of the range of `p`, extended by zero on the kernel of `p` when `p` is
idempotent: `x ↦ S (p x)`. -/
def rangeEndExtend :
    (LinearMap.range p →ₗ[Aᵐᵒᵖ] LinearMap.range p) →+ ((ι → A) →ₗ[Aᵐᵒᵖ] (ι → A)) where
  toFun S := (LinearMap.range p).subtype ∘ₗ S ∘ₗ p.rangeRestrict
  map_zero' := by ext; simp
  map_add' S S' := by ext; simp

@[simp]
theorem rangeEndExtend_apply (S : LinearMap.range p →ₗ[Aᵐᵒᵖ] LinearMap.range p)
    (x : ι → A) : rangeEndExtend p S x = S (p.rangeRestrict x) :=
  (rfl)

variable {p}

/-- For an idempotent `p`, extension by zero is multiplicative. -/
theorem rangeEndExtend_mul (hp : IsIdempotentElem p)
    (S S' : LinearMap.range p →ₗ[Aᵐᵒᵖ] LinearMap.range p) :
    rangeEndExtend p (S * S') = rangeEndExtend p S * rangeEndExtend p S' := by
  refine LinearMap.ext fun x ↦ ?_
  simp [LinearMap.IsIdempotentElem.rangeRestrict_coe hp]

/-- For an idempotent `p`, the extension by zero of an endomorphism of the range of `p` vanishes
on the kernel of `p`. -/
theorem rangeEndExtend_mul_proj (hp : IsIdempotentElem p)
    (S : LinearMap.range p →ₗ[Aᵐᵒᵖ] LinearMap.range p) :
    rangeEndExtend p S * p = rangeEndExtend p S := by
  refine LinearMap.ext fun x ↦ ?_
  simp [LinearMap.IsIdempotentElem.rangeRestrict_apply_self hp]

/-- For an idempotent `p`, the extension by zero of an endomorphism of the range of `p` takes
values in the range of `p`, so `p` fixes its values. -/
theorem apply_rangeEndExtend (hp : IsIdempotentElem p)
    (S : LinearMap.range p →ₗ[Aᵐᵒᵖ] LinearMap.range p) (x : ι → A) :
    p (rangeEndExtend p S x) = rangeEndExtend p S x := by
  rw [rangeEndExtend_apply]
  exact (LinearMap.IsIdempotentElem.mem_range_iff hp).mp (S _).property

/-- For an idempotent `p`, the extension by zero of an endomorphism of the range of `p` takes
values in the range of `p`. -/
theorem proj_mul_rangeEndExtend (hp : IsIdempotentElem p)
    (S : LinearMap.range p →ₗ[Aᵐᵒᵖ] LinearMap.range p) :
    p * rangeEndExtend p S = rangeEndExtend p S :=
  LinearMap.ext fun x ↦ by rw [mul_apply_eq_comp, apply_rangeEndExtend hp]

/-- The extension by zero of the derivative of `S` along the projection of the coordinate
connection is `p [D, T] p`, with `T` the extension by zero of `S`. -/
theorem rangeEndExtend_derivativeEnd_project_coordinate (hp : IsIdempotentElem p)
    (D : derivationLieAlgebra k A) (S : LinearMap.range p →ₗ[Aᵐᵒᵖ] LinearMap.range p) :
    rangeEndExtend p (derivativeEnd (project (coordinate D ι) p hp) S) =
      p * derivativeEnd (coordinate D ι) (rangeEndExtend p S) * p := by
  refine LinearMap.ext fun x ↦ ?_
  have hg : project (coordinate D ι) p hp (p.rangeRestrict x) =
      p.rangeRestrict (coordinate D ι (p x)) :=
    Subtype.ext (coe_project_apply _ _ _ _)
  rw [rangeEndExtend_apply]
  simp only [mul_apply_eq_comp, derivativeEnd_apply, map_sub, apply_rangeEndExtend hp]
  simp [hg, LinearMap.IsIdempotentElem.rangeRestrict_apply_self hp]

variable [Fintype ι] [DecidableEq ι] (p)

/-- The `τ`-trace of a right-module endomorphism of the range of `p`: the trace on `ι → A` of
its extension `x ↦ S (p x)`. For an idempotent `p` this is the extension by zero on the kernel
of `p`. -/
def rangeEndTrace : (LinearMap.range p →ₗ[Aᵐᵒᵖ] LinearMap.range p) →+ M :=
  (piEndTrace τ).comp (rangeEndExtend p)

theorem rangeEndTrace_apply (S : LinearMap.range p →ₗ[Aᵐᵒᵖ] LinearMap.range p) :
    rangeEndTrace τ p S = piEndTrace τ (rangeEndExtend p S) :=
  (rfl)

variable {τ p}

/-- The `τ`-trace on the range of an idempotent vanishes on commutators. -/
theorem rangeEndTrace_mul_comm (hτ : ∀ x y, τ (x * y) = τ (y * x)) (hp : IsIdempotentElem p)
    (S S' : LinearMap.range p →ₗ[Aᵐᵒᵖ] LinearMap.range p) :
    rangeEndTrace τ p (S * S') = rangeEndTrace τ p (S' * S) := by
  simp only [rangeEndTrace_apply, rangeEndExtend_mul hp, piEndTrace_mul_comm hτ]

/-- Integration by parts on the range of an idempotent: if `τ ∘ D = 0`, the trace of the
derivative `[c, S]` of an endomorphism along any connection `c` along `D` vanishes. -/
theorem rangeEndTrace_derivativeEnd_eq_zero (hτ : ∀ x y, τ (x * y) = τ (y * x))
    (hp : IsIdempotentElem p) {D : derivationLieAlgebra k A}
    (hD : ∀ x, τ ((D : Module.End k A) x) = 0)
    (c : RightConnection (E := LinearMap.range p) D)
    (S : LinearMap.range p →ₗ[Aᵐᵒᵖ] LinearMap.range p) :
    rangeEndTrace τ p (derivativeEnd c S) = 0 := by
  set g := project (coordinate D ι) p hp
  -- Reduce to the projected coordinate connection: the two derivatives differ by a commutator.
  have hcg : rangeEndTrace τ p (derivativeEnd c S) = rangeEndTrace τ p (derivativeEnd g S) := by
    rw [← sub_eq_zero, ← map_sub, derivativeEnd_sub_derivativeEnd]
    rw [map_sub (rangeEndTrace τ p), rangeEndTrace_mul_comm hτ hp, sub_self]
  rw [hcg, rangeEndTrace_apply, rangeEndExtend_derivativeEnd_project_coordinate hp]
  set T := rangeEndExtend p S
  set d := derivativeEnd (coordinate D ι) p
  have hTp : T * p = T := rangeEndExtend_mul_proj hp S
  have hpT : p * T = T := proj_mul_rangeEndExtend hp S
  -- `p [D, p] p = 0` since `[D, p]` maps the range of `p` into its kernel.
  have hpdp : p * (d * p) = 0 :=
    LinearMap.ext fun x ↦
      apply_derivativeEnd_self_apply_eq_zero (coordinate D ι) hp ⟨p x, p.mem_range_self x⟩
  -- `p [D, T] p` has the trace of `[D, T] p = [D, T] - T [D, p]`, and `T [D, p]` has the trace
  -- of `T p [D, p] p = 0`.
  have h₁ : piEndTrace τ (p * derivativeEnd (coordinate D ι) T * p) =
      piEndTrace τ (derivativeEnd (coordinate D ι) T * p) := by
    rw [mul_assoc, piEndTrace_mul_comm hτ, mul_assoc, hp.eq]
  have h₂ : derivativeEnd (coordinate D ι) T * p = derivativeEnd (coordinate D ι) T - T * d := by
    rw [eq_sub_iff_add_eq, ← derivativeEnd_mul, hTp]
  have h₃ : piEndTrace τ (T * d) = 0 :=
    calc piEndTrace τ (T * d) = piEndTrace τ (p * (T * p * d)) := by
          rw [hTp, ← mul_assoc, hpT]
      _ = piEndTrace τ (T * (p * (d * p))) := by
          rw [piEndTrace_mul_comm hτ p]
          simp only [mul_assoc]
      _ = 0 := by rw [hpdp, mul_zero, map_zero]
  rw [h₁, h₂, map_sub, piEndTrace_derivativeEnd_coordinate_eq_zero hD, h₃, sub_zero]

variable {D₁ D₂ : derivationLieAlgebra k A}

/-- **Independence of the connection.** If `τ ∘ D₁ = 0` and `τ ∘ D₂ = 0`, the trace of the
curvature of connections along `D₁` and `D₂` on the range of an idempotent does not depend on
the connections. -/
theorem rangeEndTrace_curvature_eq (hτ : ∀ x y, τ (x * y) = τ (y * x))
    (hp : IsIdempotentElem p)
    (hD₁ : ∀ x, τ ((D₁ : Module.End k A) x) = 0) (hD₂ : ∀ x, τ ((D₂ : Module.End k A) x) = 0)
    (hD : Commute (D₁ : Module.End k A) (D₂ : Module.End k A))
    (c₁ c₁' : RightConnection (E := LinearMap.range p) D₁)
    (c₂ c₂' : RightConnection (E := LinearMap.range p) D₂) :
    rangeEndTrace τ p (curvature c₁ c₂ hD) = rangeEndTrace τ p (curvature c₁' c₂' hD) := by
  rw [curvature_eq_curvature_add c₁ c₁' c₂ c₂']
  -- `simp` only unifies the subtraction coming from `curvature_eq_curvature_add` with `map_sub`
  -- once the map is given explicitly.
  simp only [map_add, map_sub (rangeEndTrace τ p), rangeEndTrace_derivativeEnd_eq_zero hτ hp hD₁,
    rangeEndTrace_derivativeEnd_eq_zero hτ hp hD₂, rangeEndTrace_mul_comm hτ hp]
  abel

/-- The trace of the curvature of the projected coordinate connections on the range of an
idempotent `p` is the trace of `p ([D₁, p] [D₂, p] - [D₂, p] [D₁, p])`. -/
theorem rangeEndTrace_curvature_project_coordinate (hτ : ∀ x y, τ (x * y) = τ (y * x))
    (hp : IsIdempotentElem p) (hD : Commute (D₁ : Module.End k A) (D₂ : Module.End k A)) :
    rangeEndTrace τ p
        (curvature (project (coordinate D₁ ι) p hp) (project (coordinate D₂ ι) p hp) hD) =
      piEndTrace τ (p * (derivativeEnd (coordinate D₁ ι) p * derivativeEnd (coordinate D₂ ι) p -
        derivativeEnd (coordinate D₂ ι) p * derivativeEnd (coordinate D₁ ι) p)) := by
  set Ω := derivativeEnd (coordinate D₁ ι) p * derivativeEnd (coordinate D₂ ι) p -
    derivativeEnd (coordinate D₂ ι) p * derivativeEnd (coordinate D₁ ι) p
  have hext : rangeEndExtend p
      (curvature (project (coordinate D₁ ι) p hp) (project (coordinate D₂ ι) p hp) hD) =
      p * Ω * p := by
    refine LinearMap.ext fun x ↦ ?_
    simpa [Ω] using coe_curvature_project_of_flat (coordinate D₁ ι) (coordinate D₂ ι) hD
      (curvature_coordinate ι hD) p hp (p.rangeRestrict x)
  rw [rangeEndTrace_apply, hext, mul_assoc, piEndTrace_mul_comm hτ, mul_assoc,
    hp.eq, piEndTrace_mul_comm hτ]

end Range

/-! ### The curvature-trace formula -/

section CurvatureTrace

variable [Module k M] [Fintype ι] [DecidableEq ι] {τ : A →ₗ[k] M}
  {D₁ D₂ : derivationLieAlgebra k A}

/-- **The curvature-trace formula.** Let `τ` be a trace and `D₁, D₂` commuting derivations with
`τ ∘ Dⱼ = 0`. For any connections `c₁, c₂` along `D₁, D₂` on the range of an idempotent matrix
`e` acting on `ι → A` by left multiplication, the `τ`-trace of the curvature `[c₁, c₂]` is the
matrix extension `φ#Tr` of `φ (a₀, a₁, a₂) = τ (a₀ (D₁a₁ D₂a₂ - D₂a₁ D₁a₂))` evaluated at
`(e, e, e)`. -/
theorem rangeEndTrace_curvature_eq_matrixCochainExtension
    (hτ : ∀ x y, τ (x * y) = τ (y * x))
    (hD₁ : ∀ x, τ ((D₁ : Module.End k A) x) = 0) (hD₂ : ∀ x, τ ((D₂ : Module.End k A) x) = 0)
    (hD : Commute (D₁ : Module.End k A) (D₂ : Module.End k A))
    {e : Matrix ι ι A} (he : IsIdempotentElem e)
    (c₁ : RightConnection (E := LinearMap.range (Matrix.mulVecBilin A Aᵐᵒᵖ e)) D₁)
    (c₂ : RightConnection (E := LinearMap.range (Matrix.mulVecBilin A Aᵐᵒᵖ e)) D₂) :
    rangeEndTrace (τ : A →+ M) (Matrix.mulVecBilin A Aᵐᵒᵖ e) (curvature c₁ c₂ hD) =
      matrixCochainExtension ι 2 (traceDerivationPairCochain τ D₁ D₂) ![e, e, e] := by
  have hp := he.mulVecBilin A Aᵐᵒᵖ
  rw [rangeEndTrace_curvature_eq hτ hp hD₁ hD₂ hD c₁ (project (coordinate D₁ ι) _ hp) c₂
      (project (coordinate D₂ ι) _ hp), rangeEndTrace_curvature_project_coordinate hτ hp hD,
    derivativeEnd_coordinate_mulVecBilin, derivativeEnd_coordinate_mulVecBilin]
  simp only [Module.End.mul_eq_comp, ← Matrix.mulVecBilin_mul, ← map_sub]
  rw [piEndTrace_mulVecBilin, matrixCochainExtension_apply, Fintype.sum_finThreeArrow]
  simp [Matrix.trace, Matrix.mul_apply, Matrix.sub_apply, map_sum, Finset.mul_sum, mul_sub,
    Finset.sum_sub_distrib]

end CurvatureTrace

end TauCeti
