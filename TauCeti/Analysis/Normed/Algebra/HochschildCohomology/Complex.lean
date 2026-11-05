/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Algebra.HochschildCohomology.Coboundary
public import TauCeti.Algebra.Homology.ModuleCat.Basic

/-!
# Bounded Hochschild cohomology

The bounded Hochschild differential makes the continuous multilinear cochains of a possibly
nonunital normed algebra into a cochain complex of vector spaces. Its cocycles are the kernel
of the differential; its coboundaries are zero in degree zero and the range of the preceding
differential otherwise. The cohomology is their algebraic quotient, without taking the closure
of the coboundaries. In particular, no Hausdorff or Banach structure is asserted on cohomology.

The coefficient actions are the bounded bilinear maps `L R : A →L[𝕜] E →L[𝕜] E` used by
`ContinuousLinearMap.hochschildBimoduleCoboundary`. They need not be unital or contractive.
Neither completeness nor a unit of the algebra is needed here.

The class map and its universal property use the general module-complex API. In degree zero
classes identify with central elements of the bimodule. In degree one the zero-class and
equality criteria identify cohomology with bounded derivations modulo inner derivations.
These criteria also express vanishing of the first cohomology as innerness of every bounded
derivation, without imposing closedness on the space of inner derivations.

## References

* B. E. Johnson, *Cohomology in Banach algebras*, Mem. Amer. Math. Soc. 127 (1972).
* H. G. Dales, *Banach Algebras and Automatic Continuity*, §2.8.
-/

public section

noncomputable section

open CategoryTheory

namespace ContinuousLinearMap

variable {𝕜 A E : Type*} [NontriviallyNormedField 𝕜] [NonUnitalNormedRing A]
  [NormedSpace 𝕜 A] [IsScalarTower 𝕜 A A] [SMulCommClass 𝕜 A A]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  (L R : A →L[𝕜] E →L[𝕜] E)

/-- The bounded Hochschild cocycles, the kernel of the outgoing differential. -/
def hochschildBimoduleCocycles (n : ℕ) :
    Submodule 𝕜 (ContinuousMultilinearMap 𝕜 (fun _ : Fin n ↦ A) E) :=
  (hochschildBimoduleCoboundary L R n).ker

/-- Membership in the bounded cocycles means that the differential vanishes. -/
@[simp]
theorem mem_hochschildBimoduleCocycles_iff {n : ℕ}
    {T : ContinuousMultilinearMap 𝕜 (fun _ : Fin n ↦ A) E} :
    T ∈ hochschildBimoduleCocycles L R n ↔ hochschildBimoduleCoboundary L R n T = 0 :=
  LinearMap.mem_ker

/-- The bounded Hochschild coboundaries: zero in degree zero, and the range of the preceding
differential in positive degree. The range is not replaced by its closure. -/
def hochschildBimoduleCoboundaries :
    (n : ℕ) → Submodule 𝕜 (ContinuousMultilinearMap 𝕜 (fun _ : Fin n ↦ A) E)
  | 0 => ⊥
  | n + 1 => (hochschildBimoduleCoboundary L R n).range

/-- There are no nonzero degree-zero coboundaries. -/
@[simp]
theorem hochschildBimoduleCoboundaries_zero : hochschildBimoduleCoboundaries L R 0 = ⊥ :=
  (rfl)

/-- In positive degree the coboundaries are the range of the preceding differential. -/
theorem hochschildBimoduleCoboundaries_succ (n : ℕ) :
    hochschildBimoduleCoboundaries L R (n + 1) = (hochschildBimoduleCoboundary L R n).range :=
  (rfl)

/-- A positive-degree coboundary is the differential of a bounded cochain. -/
@[simp]
theorem mem_hochschildBimoduleCoboundaries_succ_iff {n : ℕ}
    {T : ContinuousMultilinearMap 𝕜 (fun _ : Fin (n + 1) ↦ A) E} :
    T ∈ hochschildBimoduleCoboundaries L R (n + 1) ↔
      ∃ S, hochschildBimoduleCoboundary L R n S = T :=
  LinearMap.mem_range

variable (hL : ∀ a b x, L (a * b) x = L a (L b x))
  (hR : ∀ a b x, R (a * b) x = R b (R a x))
  (hLR : ∀ a b x, L a (R b x) = R b (L a x))

include hL hR hLR in
/-- Every bounded Hochschild coboundary is a cocycle. -/
theorem hochschildBimoduleCoboundaries_le_cocycles (n : ℕ) :
    hochschildBimoduleCoboundaries L R n ≤ hochschildBimoduleCocycles L R n := by
  cases n with
  | zero => exact bot_le
  | succ n =>
    rintro _ ⟨S, rfl⟩
    exact hochschildBimoduleCoboundary_hochschildBimoduleCoboundary L R hL hR hLR S

/-- The bounded Hochschild cochain complex, viewed as a complex of vector spaces. -/
def hochschildBimoduleCochainComplex : CochainComplex (ModuleCat 𝕜) ℕ :=
  CochainComplex.of
    (fun n ↦ ModuleCat.of 𝕜 (ContinuousMultilinearMap 𝕜 (fun _ : Fin n ↦ A) E))
    (fun n ↦ ModuleCat.ofHom (hochschildBimoduleCoboundary L R n).toLinearMap)
    fun _ ↦ ModuleCat.hom_ext <| congrArg ContinuousLinearMap.toLinearMap
      (hochschildBimoduleCoboundary_comp_hochschildBimoduleCoboundary L R hL hR hLR)

/-- The degree-`n` term is the space of bounded `n`-multilinear cochains. -/
def hochschildBimoduleCochainComplexXIso (n : ℕ) :
    (hochschildBimoduleCochainComplex L R hL hR hLR).X n ≅
      ModuleCat.of 𝕜 (ContinuousMultilinearMap 𝕜 (fun _ : Fin n ↦ A) E) :=
  Iso.refl _

/-- The complex differential is the bounded Hochschild differential under the term
identifications. -/
@[reassoc, elementwise]
theorem hochschildBimoduleCochainComplex_d (n : ℕ) :
    (hochschildBimoduleCochainComplex L R hL hR hLR).d n (n + 1) ≫
        (hochschildBimoduleCochainComplexXIso L R hL hR hLR (n + 1)).hom =
      (hochschildBimoduleCochainComplexXIso L R hL hR hLR n).hom ≫
        ModuleCat.ofHom (hochschildBimoduleCoboundary L R n).toLinearMap := by
  simp [hochschildBimoduleCochainComplex, hochschildBimoduleCochainComplexXIso]

/-- Bounded Hochschild cohomology as a vector-space quotient of cocycles by coboundaries.
No closure is taken and no separated topology is asserted. -/
abbrev hochschildBimoduleCohomology (n : ℕ) : ModuleCat 𝕜 :=
  (hochschildBimoduleCochainComplex L R hL hR hLR).homology n

private theorem mem_cocycles_iff_complex (n : ℕ)
    (T : ContinuousMultilinearMap 𝕜 (fun _ : Fin n ↦ A) E) :
    T ∈ hochschildBimoduleCocycles L R n ↔
      (hochschildBimoduleCochainComplex L R hL hR hLR).d n (n + 1)
        ((hochschildBimoduleCochainComplexXIso L R hL hR hLR n).inv T) = 0 := by
  rw [mem_hochschildBimoduleCocycles_iff,
    (hochschildBimoduleCochainComplex L R hL hR hLR).moduleCat_d_inv_eq_zero_iff
      (fun n ↦ (hochschildBimoduleCoboundary L R n).toLinearMap)
      (hochschildBimoduleCochainComplex_d L R hL hR hLR)]
  rfl

private theorem mem_coboundaries_iff_complex (n : ℕ)
    (T : ContinuousMultilinearMap 𝕜 (fun _ : Fin n ↦ A) E) :
    T ∈ hochschildBimoduleCoboundaries L R n ↔
      ∃ y : (hochschildBimoduleCochainComplex L R hL hR hLR).X
          ((ComplexShape.up ℕ).prev n),
        (hochschildBimoduleCochainComplex L R hL hR hLR).d
          ((ComplexShape.up ℕ).prev n) n y =
            (hochschildBimoduleCochainComplexXIso L R hL hR hLR n).inv T :=
  (hochschildBimoduleCochainComplex L R hL hR hLR).moduleCat_mem_iff_exists_d_eq_inv
    (hochschildBimoduleCoboundaries L R)
    (fun n ↦ (hochschildBimoduleCoboundary L R n).toLinearMap)
    (hochschildBimoduleCochainComplex_d L R hL hR hLR)
    (hochschildBimoduleCoboundaries_zero L R) (hochschildBimoduleCoboundaries_succ L R) n T

namespace hochschildBimoduleCohomology

/-- The cohomology class of a bounded cocycle. -/
def mk (n : ℕ) : hochschildBimoduleCocycles L R n →ₗ[𝕜]
    hochschildBimoduleCohomology L R hL hR hLR n :=
  (hochschildBimoduleCochainComplex L R hL hR hLR).moduleCatCohomologyClassOfIso
    (fun n ↦ ContinuousMultilinearMap 𝕜 (fun _ : Fin n ↦ A) E)
    (hochschildBimoduleCocycles L R) (hochschildBimoduleCochainComplexXIso L R hL hR hLR)
    (mem_cocycles_iff_complex L R hL hR hLR) n

/-- Every cohomology class has a bounded cocycle representative. -/
theorem mk_surjective (n : ℕ) : Function.Surjective (mk L R hL hR hLR n) :=
  (hochschildBimoduleCochainComplex L R hL hR hLR).moduleCatCohomologyClassOfIso_surjective
    (fun n ↦ ContinuousMultilinearMap 𝕜 (fun _ : Fin n ↦ A) E)
    (hochschildBimoduleCocycles L R) (hochschildBimoduleCochainComplexXIso L R hL hR hLR)
    (mem_cocycles_iff_complex L R hL hR hLR) n

/-- A bounded cocycle represents zero exactly when it is a coboundary. -/
@[simp]
theorem mk_eq_zero_iff (n : ℕ) (T : hochschildBimoduleCocycles L R n) :
    mk L R hL hR hLR n T = 0 ↔
      (T : ContinuousMultilinearMap 𝕜 (fun _ : Fin n ↦ A) E) ∈
        hochschildBimoduleCoboundaries L R n :=
  (hochschildBimoduleCochainComplex L R hL hR hLR).moduleCatCohomologyClassOfIso_eq_zero_iff
    (fun n ↦ ContinuousMultilinearMap 𝕜 (fun _ : Fin n ↦ A) E)
    (hochschildBimoduleCocycles L R) (hochschildBimoduleCoboundaries L R)
    (hochschildBimoduleCochainComplexXIso L R hL hR hLR)
    (mem_cocycles_iff_complex L R hL hR hLR) (mem_coboundaries_iff_complex L R hL hR hLR) n T

/-- Two bounded cocycles have the same class exactly when their difference is a coboundary. -/
theorem mk_eq_mk_iff (n : ℕ) (T S : hochschildBimoduleCocycles L R n) :
    mk L R hL hR hLR n T = mk L R hL hR hLR n S ↔
      (T : ContinuousMultilinearMap 𝕜 (fun _ : Fin n ↦ A) E) - S ∈
        hochschildBimoduleCoboundaries L R n :=
  (hochschildBimoduleCochainComplex L R hL hR hLR).moduleCatCohomologyClassOfIso_eq_iff
    (fun n ↦ ContinuousMultilinearMap 𝕜 (fun _ : Fin n ↦ A) E)
    (hochschildBimoduleCocycles L R) (hochschildBimoduleCoboundaries L R)
    (hochschildBimoduleCochainComplexXIso L R hL hR hLR)
    (mem_cocycles_iff_complex L R hL hR hLR) (mem_coboundaries_iff_complex L R hL hR hLR) n T S

variable {L R hL hR hLR} {F : Type*} [AddCommGroup F] [Module 𝕜 F]

/-- Linear maps out of bounded cohomology are determined by cocycle classes. -/
@[ext]
theorem linearMap_ext {n : ℕ}
    {f g : hochschildBimoduleCohomology L R hL hR hLR n →ₗ[𝕜] F}
    (h : f ∘ₗ mk L R hL hR hLR n = g ∘ₗ mk L R hL hR hLR n) : f = g :=
  LinearMap.ext fun z ↦ by
    obtain ⟨T, rfl⟩ := mk_surjective L R hL hR hLR n z
    exact LinearMap.congr_fun h T

/-- A linear map on bounded cocycles descends to cohomology if it vanishes on coboundaries. -/
def desc (n : ℕ) (f : hochschildBimoduleCocycles L R n →ₗ[𝕜] F)
    (hf : ∀ T : hochschildBimoduleCocycles L R n,
      (T : ContinuousMultilinearMap 𝕜 (fun _ : Fin n ↦ A) E) ∈
        hochschildBimoduleCoboundaries L R n → f T = 0) :
    hochschildBimoduleCohomology L R hL hR hLR n →ₗ[𝕜] F :=
  (mk L R hL hR hLR n).liftOfSurjective (mk_surjective L R hL hR hLR n)
    ⟨f, fun T hT ↦ LinearMap.mem_ker.2
      (hf T ((mk_eq_zero_iff L R hL hR hLR n T).1 (LinearMap.mem_ker.1 hT)))⟩

/-- The descended map evaluates on a class by evaluating its representative. -/
@[simp]
theorem desc_mk (n : ℕ) (f : hochschildBimoduleCocycles L R n →ₗ[𝕜] F)
    (hf : ∀ T : hochschildBimoduleCocycles L R n,
      (T : ContinuousMultilinearMap 𝕜 (fun _ : Fin n ↦ A) E) ∈
        hochschildBimoduleCoboundaries L R n → f T = 0)
    (T : hochschildBimoduleCocycles L R n) :
    desc n f hf (mk L R hL hR hLR n T) = f T :=
  LinearMap.equivOfSurjective_apply _ _

end hochschildBimoduleCohomology

/-- A bounded one-cochain is a coboundary exactly when it is an inner derivation. -/
theorem mem_hochschildBimoduleCoboundaries_one_iff
    (T : ContinuousMultilinearMap 𝕜 (fun _ : Fin 1 ↦ A) E) :
    T ∈ hochschildBimoduleCoboundaries L R 1 ↔
      ∃ x : E, ∀ a : A, T (fun _ ↦ a) = L a x - R a x := by
  rw [mem_hochschildBimoduleCoboundaries_succ_iff]
  constructor
  · rintro ⟨S, rfl⟩
    obtain ⟨x, rfl⟩ := (continuousMultilinearCurryFin0 𝕜 A E).symm.surjective S
    exact ⟨x, fun a ↦ hochschildBimoduleCoboundary_constOfIsEmpty L R x (fun _ ↦ a)⟩
  · rintro ⟨x, hx⟩
    refine ⟨ContinuousMultilinearMap.constOfIsEmpty 𝕜 (fun _ : Fin 0 ↦ A) x, ?_⟩
    ext a
    rw [hochschildBimoduleCoboundary_constOfIsEmpty]
    have ha : (fun _ : Fin 1 ↦ a 0) = a :=
      funext fun i ↦ congrArg a (Subsingleton.elim 0 i)
    simpa only [ha] using (hx (a 0)).symm

namespace hochschildBimoduleCohomology

/-- The first cohomology class vanishes precisely for inner derivations. -/
theorem mk_one_eq_zero_iff (T : hochschildBimoduleCocycles L R 1) :
    mk L R hL hR hLR 1 T = 0 ↔
      ∃ x : E, ∀ a : A, T.val (fun _ ↦ a) = L a x - R a x := by
  rw [mk_eq_zero_iff, mem_hochschildBimoduleCoboundaries_one_iff]

/-- Two bounded derivations represent the same first cohomology class precisely when their
difference is inner. -/
theorem mk_one_eq_mk_one_iff (T S : hochschildBimoduleCocycles L R 1) :
    mk L R hL hR hLR 1 T = mk L R hL hR hLR 1 S ↔
      ∃ x : E, ∀ a : A, T.val (fun _ ↦ a) - S.val (fun _ ↦ a) = L a x - R a x := by
  rw [mk_eq_mk_iff, mem_hochschildBimoduleCoboundaries_one_iff]
  rfl

/-- Vanishing of the first bounded cohomology is equivalent to innerness of every bounded
derivation, with the given possibly nonunital, noncontractive bimodule actions. -/
theorem subsingleton_one_iff :
    Subsingleton (hochschildBimoduleCohomology L R hL hR hLR 1) ↔
      ∀ D : A →L[𝕜] E, (∀ a b, D (a * b) = L a (D b) + R b (D a)) →
        ∃ x : E, ∀ a, D a = L a x - R a x := by
  constructor
  · intro h D hD
    let T : hochschildBimoduleCocycles L R 1 :=
      ⟨ContinuousMultilinearMap.ofSubsingleton 𝕜 A E 0 D,
        (hochschildBimoduleCoboundary_ofSubsingleton_eq_zero_iff L R D).2 hD⟩
    obtain ⟨x, hx⟩ := (mk_one_eq_zero_iff L R hL hR hLR T).1 (h.elim _ _)
    exact ⟨x, hx⟩
  · intro h
    suffices hz : ∀ z : hochschildBimoduleCohomology L R hL hR hLR 1, z = 0 from
      ⟨fun x y ↦ (hz x).trans (hz y).symm⟩
    intro z
    obtain ⟨T, rfl⟩ := mk_surjective L R hL hR hLR 1 z
    obtain ⟨D, hD⟩ :=
      (ContinuousMultilinearMap.ofSubsingletonₗᵢ 𝕜 A (G' := E) (0 : Fin 1)).surjective T.val
    have hd : ∀ a b, D (a * b) = L a (D b) + R b (D a) :=
      (hochschildBimoduleCoboundary_ofSubsingleton_eq_zero_iff L R D).1
        (hD.symm ▸ T.property)
    obtain ⟨x, hx⟩ := h D hd
    apply (mk_one_eq_zero_iff L R hL hR hLR T).2
    exact ⟨x, fun a ↦ by rw [← hD]; exact hx a⟩

/-- In degree zero the class map is a linear equivalence: there are no coboundaries. -/
private def zeroCocyclesEquiv : hochschildBimoduleCocycles L R 0 ≃ₗ[𝕜]
    hochschildBimoduleCohomology L R hL hR hLR 0 :=
  LinearEquiv.ofBijective (mk L R hL hR hLR 0) ⟨by
    intro T S h
    apply Subtype.ext
    have hs := (mk_eq_mk_iff L R hL hR hLR 0 T S).1 h
    exact sub_eq_zero.mp (by
      simpa only [hochschildBimoduleCoboundaries_zero, Submodule.mem_bot] using hs),
    mk_surjective L R hL hR hLR 0⟩

/-- Degree-zero bounded cohomology is the centre of the coefficient bimodule, realized as
`ker (x ↦ (a ↦ L a x - R a x))`. -/
def zeroEquiv : hochschildBimoduleCohomology L R hL hR hLR 0 ≃ₗ[𝕜] (L - R).flip.ker :=
  (zeroCocyclesEquiv L R hL hR hLR).symm.trans <|
    (continuousMultilinearCurryFin0 𝕜 A E).toLinearEquiv.ofSubmodules
      (hochschildBimoduleCocycles L R 0) (L - R).flip.ker (by
        rw [Submodule.map_equiv_eq_comap_symm]
        ext x
        simp only [Submodule.mem_comap, LinearEquiv.coe_coe,
          LinearIsometryEquiv.coe_symm_toLinearEquiv,
          continuousMultilinearCurryFin0_symm_apply, ContinuousMultilinearMap.uncurry0,
          mem_hochschildBimoduleCocycles_iff,
          hochschildBimoduleCoboundary_constOfIsEmpty_eq_zero_iff, LinearMap.mem_ker]
        constructor
        · intro h
          ext a
          exact sub_eq_zero.mpr (h a)
        · intro h a
          exact sub_eq_zero.mp (congrArg (fun f : A →L[𝕜] E ↦ f a) h))

/-- The degree-zero identification evaluates a representative on the empty tuple. -/
@[simp]
theorem zeroEquiv_mk (T : hochschildBimoduleCocycles L R 0) :
    (zeroEquiv L R hL hR hLR (mk L R hL hR hLR 0 T) : E) = T.val 0 := by
  have h : mk L R hL hR hLR 0 T = zeroCocyclesEquiv L R hL hR hLR T := (rfl)
  simp only [zeroEquiv, LinearEquiv.trans_apply, h, LinearEquiv.symm_apply_apply,
    LinearEquiv.ofSubmodules_apply, LinearIsometryEquiv.coe_toLinearEquiv,
    continuousMultilinearCurryFin0_apply]

end hochschildBimoduleCohomology

end ContinuousLinearMap
