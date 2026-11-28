/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.CMField.UnitaryGroup.AdelicFrame
public import TauCeti.LinearAlgebra.Matrix.IndefiniteUnitaryGroup.IsotropicSplitting.Transfer

/-!
# Adelic frames of a rational isotropic splitting

Let `E` be a CM field, `V = (J, x)` and `V₀ = (J₀, x₀)` hermitian spaces with adelic frames of
signs `s` and `s₀` (`TauCeti.FramedHermitianSpace`), and `D = (k, l, ι)` a rational isotropic
splitting of `J` over `J₀` along `p` (`TauCeti.IsotropicSplitting`), that is a Witt decomposition
`E^n = l E^p ⊕ ι E^{n₀} ⊕ k E^p` with dual isotropic frames `k`, `l` and `ι* J ι = J₀`.

Read in the adelic frames, `D` becomes a splitting of the standard forms: its **adelic frames**
are `x⁻¹ k`, `x⁻¹ l` and `x⁻¹ ι x₀`, which split `diag(s)` over `diag(s₀)` at the infinite places
(`TauCeti.IsotropicSplitting.infiniteSplitting`) and `1_n` over `1_{n₀}` at the finite places
(`TauCeti.IsotropicSplitting.finiteSplitting`). Their Levi and unipotent elements give elements of
the adelic unitary group `G(s)`:

* the **adelic Levi element** `m(a, g₀)` (`TauCeti.IsotropicSplitting.adelicLevi`), for
  `a ∈ GL_p(𝔸)` and `g₀ ∈ G(s₀)`, acting by `a` on the adelic frame `k`, by `g₀` on the core and
  by `(a⁻¹)*` on the adelic frame `l`;
* the **adelic unipotent element** `n(c, b)` (`TauCeti.IsotropicSplitting.adelicUnipotent`), for
  adelic matrices `c` and `b`, fixing the adelic frame `k`.

Here `GL_p(𝔸)` and the adelic matrices are written by their archimedean and finite components.

## Main results

* `TauCeti.IsotropicSplitting.adelicLevi_eq_rationalEmbedding`: for rational `a` and a rational
  point `g₀ = x₀⁻¹ γ x₀`, the adelic Levi element is the rational point `x⁻¹ m(a, γ) x`, so it lies
  in `Γ_V` (`TauCeti.IsotropicSplitting.adelicLevi_mem_rationalPoints`).
* `TauCeti.IsotropicSplitting.adelicUnipotent_eq_rationalEmbedding`: for rational `c` and `b`, the
  adelic unipotent element of `(x₀⁻¹ c, b)` is the rational point `x⁻¹ n(c, b) x`, so it lies in
  `Γ_V` (`TauCeti.IsotropicSplitting.adelicUnipotent_mem_rationalPoints`).
* `TauCeti.IsotropicSplitting.adelicUnipotent_mul_adelicUnipotent`: the group law
  `n(c, b) n(c', b') = n(c + c', b + j c* ε c' + b')` of the adelic unipotent elements, `ε` the
  standard form of signs `s₀`.

## Attribution

The adelic frames and the rationality statements follow `New.Space.Splitting.kAdelic`,
`New.Space.Splitting.lAdelic`, `New.Space.Splitting.iAdelic`, `New.Space.Splitting.levi`,
`New.Space.Splitting.radicalElement`, `New.Space.Splitting.levi_mem_Gamma` and
`New.Space.Splitting.radicalElement_mem_Gamma` in the file
`src/Lib/Weil/MixedModel/IsotropicSplitting.lean` of grh-lean
(https://github.com/lsernau/grh-lean, Apache 2.0, Copyright 2026 Anthropic, PBC), where the adele
ring is a single ring; here the archimedean and finite components are treated separately, through
the base change and pullback of splittings.

## References

* M.-A. Knus, *Quadratic and Hermitian forms over rings* (1991), the Witt decomposition of a
  hermitian space.
-/

public section

noncomputable section

open Matrix NumberField NumberField.IsCMField
open scoped NumberField.AdeleRing

namespace TauCeti

namespace IsotropicSplitting

variable {E : Type*} [Field E] [NumberField E] [IsCMField E]
  {n n₀ p : Type*} [Fintype n] [DecidableEq n] [Fintype n₀] [DecidableEq n₀] [Fintype p]
  [DecidableEq p] {s : n → ℤˣ} {s₀ : n₀ → ℤˣ} {V : FramedHermitianSpace E s}
  {V₀ : FramedHermitianSpace E s₀} (D : IsotropicSplitting V.gram V₀.gram p)

/-! ### The adelic frames -/

/-- The **archimedean adelic frames** of a rational splitting `D` of `V` over `V₀`: the frames
`x_∞⁻¹ k`, `x_∞⁻¹ l` and the core embedding `x_∞⁻¹ ι x₀_∞`, a splitting of `diag(s)` over
`diag(s₀)` over the infinite adeles. -/
def infiniteSplitting :
    IsotropicSplitting (diagonal fun i ↦ ((s i : ℤ) : InfiniteAdeleRing E))
      (diagonal fun i ↦ ((s₀ i : ℤ) : InfiniteAdeleRing E)) p :=
  (D.map (f := algebraMap E (InfiniteAdeleRing E)) fun r ↦ algebraMap_star_comm r).pullback
    V.star_mul_gram_mul_fst V₀.star_mul_gram_mul_fst

/-- The **finite adelic frames** of a rational splitting `D` of `V` over `V₀`: the frames
`x_f⁻¹ k`, `x_f⁻¹ l` and the core embedding `x_f⁻¹ ι x₀_f`, a splitting of `1_n` over `1_{n₀}`
over the finite adeles. -/
def finiteSplitting : IsotropicSplitting (1 : Matrix n n 𝔸ᶠ[E]) (1 : Matrix n₀ n₀ 𝔸ᶠ[E]) p :=
  (D.map (f := algebraMap E 𝔸ᶠ[E]) fun r ↦ algebraMap_star_comm r).pullback
    V.star_mul_gram_mul_snd V₀.star_mul_gram_mul_snd

@[simp]
theorem infiniteSplitting_k :
    D.infiniteSplitting.k =
      (V.frame.1 : Matrix n n (InfiniteAdeleRing E))⁻¹ * D.k.map (algebraMap E _) := by
  rw [infiniteSplitting, pullback_k, map_k]

@[simp]
theorem infiniteSplitting_l :
    D.infiniteSplitting.l =
      (V.frame.1 : Matrix n n (InfiniteAdeleRing E))⁻¹ * D.l.map (algebraMap E _) := by
  rw [infiniteSplitting, pullback_l, map_l]

@[simp]
theorem infiniteSplitting_ι :
    D.infiniteSplitting.ι = (V.frame.1 : Matrix n n (InfiniteAdeleRing E))⁻¹ *
      (D.ι.map (algebraMap E _) * (V₀.frame.1 : Matrix n₀ n₀ (InfiniteAdeleRing E))) := by
  rw [infiniteSplitting, pullback_ι, map_ι]

@[simp]
theorem finiteSplitting_k :
    D.finiteSplitting.k = (V.frame.2 : Matrix n n 𝔸ᶠ[E])⁻¹ * D.k.map (algebraMap E _) := by
  rw [finiteSplitting, pullback_k, map_k]

@[simp]
theorem finiteSplitting_l :
    D.finiteSplitting.l = (V.frame.2 : Matrix n n 𝔸ᶠ[E])⁻¹ * D.l.map (algebraMap E _) := by
  rw [finiteSplitting, pullback_l, map_l]

@[simp]
theorem finiteSplitting_ι :
    D.finiteSplitting.ι = (V.frame.2 : Matrix n n 𝔸ᶠ[E])⁻¹ *
      (D.ι.map (algebraMap E _) * (V₀.frame.2 : Matrix n₀ n₀ 𝔸ᶠ[E])) := by
  rw [finiteSplitting, pullback_ι, map_ι]

/-! ### Adelic Levi elements -/

/-- The **adelic Levi homomorphism** `m : GL_p(𝔸) × G(s₀) →* G(s)` of a rational splitting:
`m(a, g₀)` acts by `a` on the adelic frame `k`, by `g₀` on the core and by `(a⁻¹)*` on the adelic
frame `l`. Here `a ∈ GL_p(𝔸)` is given by its archimedean and finite components. -/
def adelicLevi :
    (GL p (InfiniteAdeleRing E) × GL p 𝔸ᶠ[E]) × adelicUnitaryGroup E s₀ →* adelicUnitaryGroup E s :=
  let M := (GL p (InfiniteAdeleRing E) × GL p 𝔸ᶠ[E]) × adelicUnitaryGroup E s₀
  let a : M →* GL p (InfiniteAdeleRing E) × GL p 𝔸ᶠ[E] := MonoidHom.fst _ _
  let g₀ : M →* adelicUnitaryGroup E s₀ := MonoidHom.snd _ _
  let mInf : M →* GL n (InfiniteAdeleRing E) :=
    (infiniteAdelicUnitaryGroup E s).subtype.comp (D.infiniteSplitting.levi.comp
      (((MonoidHom.fst _ _).comp a).prod ((adelicUnitaryGroup.infinitePart E s₀).comp g₀)))
  let mFin : M →* GL n 𝔸ᶠ[E] :=
    (unitaryGroupOf (1 : Matrix n n 𝔸ᶠ[E])).subtype.comp (D.finiteSplitting.levi.comp
      (((MonoidHom.snd _ _).comp a).prod
        ((MulEquiv.subgroupCongr unitaryGroupOf_one.symm).toMonoidHom.comp
          ((adelicUnitaryGroup.finitePart E s₀).comp g₀))))
  (mInf.prod mFin).codRestrict (adelicUnitaryGroup E s) fun _ ↦
    ⟨(D.infiniteSplitting.levi _).property,
      (unitaryGroupOf_one (R := 𝔸ᶠ[E]) (n := n)).le (D.finiteSplitting.levi _).property⟩

/-- The archimedean component of the adelic Levi element of `((a_∞, a_f), g₀)` is the Levi element
of `(a_∞, g₀_∞)` for the archimedean adelic frames. -/
@[simp]
theorem adelicLevi_fst (x : (GL p (InfiniteAdeleRing E) × GL p 𝔸ᶠ[E]) × adelicUnitaryGroup E s₀) :
    (D.adelicLevi x : GL n (InfiniteAdeleRing E) × GL n 𝔸ᶠ[E]).1 =
      D.infiniteSplitting.levi (x.1.1, adelicUnitaryGroup.infinitePart E s₀ x.2) :=
  (rfl)

/-- The finite component of the adelic Levi element of `((a_∞, a_f), g₀)` is the Levi element of
`(a_f, g₀_f)` for the finite adelic frames, `g₀_f` read in the unitary group of `1_{n₀}`. -/
theorem adelicLevi_snd (x : (GL p (InfiniteAdeleRing E) × GL p 𝔸ᶠ[E]) × adelicUnitaryGroup E s₀) :
    (D.adelicLevi x : GL n (InfiniteAdeleRing E) × GL n 𝔸ᶠ[E]).2 =
      D.finiteSplitting.levi (x.1.2, MulEquiv.subgroupCongr unitaryGroupOf_one.symm
        (adelicUnitaryGroup.finitePart E s₀ x.2)) :=
  (rfl)

/-- **Rational Levi elements are rational points.** For `a ∈ GL_p(E)` and `γ ∈ U(J₀)(E⁺)`, the
adelic Levi element of `(a, x₀⁻¹ γ x₀)` is the image `x⁻¹ m(a, γ) x` of the Levi element of the
rational splitting. -/
theorem adelicLevi_eq_rationalEmbedding (a : GL p E) (γ : unitaryGroupOf V₀.gram) :
    D.adelicLevi ((GeneralLinearGroup.map (algebraMap E (InfiniteAdeleRing E)) a,
        GeneralLinearGroup.map (algebraMap E 𝔸ᶠ[E]) a), V₀.rationalEmbedding γ) =
      V.rationalEmbedding (D.levi (a, γ)) := by
  refine Subtype.ext (Prod.ext (Units.ext ?_) (Units.ext ?_))
  · rw [adelicLevi_fst, infiniteSplitting, val_levi_pullback (g₀ := ⟨_, map_mem_unitaryGroupOf
      (fun r ↦ algebraMap_star_comm r) γ.property⟩),
      val_levi_map _ _ _ (GeneralLinearGroup.val_map_apply _ _)]
    · simp only [FramedHermitianSpace.coe_rationalEmbedding, Units.val_mul, coe_units_inv,
        GeneralLinearGroup.val_map_apply]
    · simp only [FramedHermitianSpace.infinitePart_rationalEmbedding,
        FramedHermitianSpace.coe_infiniteRationalEmbedding, Units.val_mul, coe_units_inv,
        GeneralLinearGroup.val_map_apply]
  · rw [adelicLevi_snd, finiteSplitting, val_levi_pullback (g₀ := ⟨_, map_mem_unitaryGroupOf
      (fun r ↦ algebraMap_star_comm r) γ.property⟩),
      val_levi_map _ _ _ (GeneralLinearGroup.val_map_apply _ _)]
    · simp only [FramedHermitianSpace.coe_rationalEmbedding, Units.val_mul, coe_units_inv,
        GeneralLinearGroup.val_map_apply]
    · simp only [FramedHermitianSpace.finitePart_rationalEmbedding, MulEquiv.subgroupCongr_apply,
        FramedHermitianSpace.coe_finiteRationalEmbedding, Units.val_mul, coe_units_inv,
        GeneralLinearGroup.val_map_apply]

/-- **Rational Levi elements lie in `Γ_V`**: for `a ∈ GL_p(E)` and `g₀ ∈ Γ_{V₀}`, the adelic Levi
element of `(a, g₀)` is a rational point of `V`. -/
theorem adelicLevi_mem_rationalPoints (a : GL p E) {g₀ : adelicUnitaryGroup E s₀}
    (hg₀ : g₀ ∈ V₀.rationalPoints) :
    D.adelicLevi ((GeneralLinearGroup.map (algebraMap E (InfiniteAdeleRing E)) a,
      GeneralLinearGroup.map (algebraMap E 𝔸ᶠ[E]) a), g₀) ∈ V.rationalPoints := by
  rw [FramedHermitianSpace.rationalPoints_def, MonoidHom.mem_range] at hg₀ ⊢
  obtain ⟨γ, rfl⟩ := hg₀
  exact ⟨_, (D.adelicLevi_eq_rationalEmbedding a γ).symm⟩

/-! ### Adelic unipotent elements -/

variable [Invertible (2 : InfiniteAdeleRing E)] [Invertible (2 : 𝔸ᶠ[E])] {j : Eˣ}
  (hj : star (j : E) = -j)

/-- The **adelic unipotent element** `n(c, b)` of a rational splitting, for adelic matrices
`c ∈ M_{n₀ × p}(𝔸)` and `b ∈ M_p(𝔸)` given by their archimedean and finite components: in each
component the unipotent element of the adelic frames, which fixes the adelic frame `k`. Here `j`
is a unit of `E` with `star j = -j`, read in the infinite and in the finite adeles, and `⅟2` is
taken in both. -/
def adelicUnipotent (c : Matrix n₀ p (InfiniteAdeleRing E) × Matrix n₀ p 𝔸ᶠ[E])
    (b : Matrix p p (InfiniteAdeleRing E) × Matrix p p 𝔸ᶠ[E]) : adelicUnitaryGroup E s :=
  ⟨((D.infiniteSplitting.unipotent
      (Units.star_coe_map_eq_neg algebraMap_star_comm hj) c.1 b.1 : GL n (InfiniteAdeleRing E)),
    (D.finiteSplitting.unipotent (Units.star_coe_map_eq_neg algebraMap_star_comm hj) c.2 b.2 :
      GL n 𝔸ᶠ[E])),
    (D.infiniteSplitting.unipotent _ _ _).property,
    (unitaryGroupOf_one (R := 𝔸ᶠ[E]) (n := n)).le (D.finiteSplitting.unipotent _ _ _).property⟩

/-- The archimedean component of the adelic unipotent element of `(c, b)` is the unipotent element
of `(c_∞, b_∞)` for the archimedean adelic frames. -/
@[simp]
theorem adelicUnipotent_fst (c : Matrix n₀ p (InfiniteAdeleRing E) × Matrix n₀ p 𝔸ᶠ[E])
    (b : Matrix p p (InfiniteAdeleRing E) × Matrix p p 𝔸ᶠ[E]) :
    (D.adelicUnipotent hj c b : GL n (InfiniteAdeleRing E) × GL n 𝔸ᶠ[E]).1 =
      D.infiniteSplitting.unipotent (Units.star_coe_map_eq_neg algebraMap_star_comm hj) c.1 b.1 :=
  (rfl)

/-- The finite component of the adelic unipotent element of `(c, b)` is the unipotent element of
`(c_f, b_f)` for the finite adelic frames. -/
@[simp]
theorem adelicUnipotent_snd (c : Matrix n₀ p (InfiniteAdeleRing E) × Matrix n₀ p 𝔸ᶠ[E])
    (b : Matrix p p (InfiniteAdeleRing E) × Matrix p p 𝔸ᶠ[E]) :
    (D.adelicUnipotent hj c b : GL n (InfiniteAdeleRing E) × GL n 𝔸ᶠ[E]).2 =
      D.finiteSplitting.unipotent (Units.star_coe_map_eq_neg algebraMap_star_comm hj) c.2 b.2 :=
  (rfl)

/-- **The group law of the adelic unipotent elements**:
`n(c, b) n(c', b') = n(c + c', b + j c* ε c' + b')`, where `ε` is `diag(s₀)` at the infinite places
and `1_{n₀}` at the finite places. -/
theorem adelicUnipotent_mul_adelicUnipotent
    (c c' : Matrix n₀ p (InfiniteAdeleRing E) × Matrix n₀ p 𝔸ᶠ[E])
    (b b' : Matrix p p (InfiniteAdeleRing E) × Matrix p p 𝔸ᶠ[E]) :
    D.adelicUnipotent hj c b * D.adelicUnipotent hj c' b' =
      D.adelicUnipotent hj (c + c')
        (b.1 + algebraMap E (InfiniteAdeleRing E) j •
            (c.1ᴴ * diagonal (fun i ↦ ((s₀ i : ℤ) : InfiniteAdeleRing E)) * c'.1) + b'.1,
          b.2 + algebraMap E 𝔸ᶠ[E] j • (c.2ᴴ * c'.2) + b'.2) := by
  refine Subtype.ext (Prod.ext ?_ ?_)
  · have h := congrArg Subtype.val (D.infiniteSplitting.unipotent_mul_unipotent
      (Units.star_coe_map_eq_neg algebraMap_star_comm hj) c.1 c'.1 b.1 b'.1)
    simp only [Units.coe_map, MonoidHom.coe_ofClass] at h
    exact h
  · have h := congrArg Subtype.val (D.finiteSplitting.unipotent_mul_unipotent
      (Units.star_coe_map_eq_neg algebraMap_star_comm hj) c.2 c'.2 b.2 b'.2)
    simp only [Units.coe_map, MonoidHom.coe_ofClass, Matrix.mul_one] at h
    exact h

/-- **Rational unipotent elements are rational points.** For matrices `c` and `b` over `E`, the
adelic unipotent element of `(x₀⁻¹ c, b)` is the image `x⁻¹ n(c, b) x` of the unipotent element of
the rational splitting. -/
theorem adelicUnipotent_eq_rationalEmbedding (c : Matrix n₀ p E) (b : Matrix p p E) :
    D.adelicUnipotent hj
        ((V₀.frame.1 : Matrix n₀ n₀ (InfiniteAdeleRing E))⁻¹ * c.map (algebraMap E _),
          (V₀.frame.2 : Matrix n₀ n₀ 𝔸ᶠ[E])⁻¹ * c.map (algebraMap E _))
        (b.map (algebraMap E _), b.map (algebraMap E _)) =
      V.rationalEmbedding (D.unipotent hj c b) := by
  refine Subtype.ext (Prod.ext (Units.ext ?_) (Units.ext ?_))
  · rw [adelicUnipotent_fst, infiniteSplitting, val_unipotent_pullback,
      val_unipotent_map _ _ hj]
    simp only [FramedHermitianSpace.coe_rationalEmbedding, Units.val_mul, coe_units_inv,
      GeneralLinearGroup.val_map_apply]
  · rw [adelicUnipotent_snd, finiteSplitting, val_unipotent_pullback, val_unipotent_map _ _ hj]
    simp only [FramedHermitianSpace.coe_rationalEmbedding, Units.val_mul, coe_units_inv,
      GeneralLinearGroup.val_map_apply]

/-- **Rational unipotent elements lie in `Γ_V`**: for matrices `c` and `b` over `E`, the adelic
unipotent element of `(x₀⁻¹ c, b)` is a rational point of `V`. -/
theorem adelicUnipotent_mem_rationalPoints (c : Matrix n₀ p E) (b : Matrix p p E) :
    D.adelicUnipotent hj
        ((V₀.frame.1 : Matrix n₀ n₀ (InfiniteAdeleRing E))⁻¹ * c.map (algebraMap E _),
          (V₀.frame.2 : Matrix n₀ n₀ 𝔸ᶠ[E])⁻¹ * c.map (algebraMap E _))
        (b.map (algebraMap E _), b.map (algebraMap E _)) ∈ V.rationalPoints := by
  rw [FramedHermitianSpace.rationalPoints_def, MonoidHom.mem_range]
  exact ⟨_, (D.adelicUnipotent_eq_rationalEmbedding hj c b).symm⟩

end IsotropicSplitting

end TauCeti
