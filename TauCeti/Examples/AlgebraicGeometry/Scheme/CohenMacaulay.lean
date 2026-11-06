/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.KrullDimension.Polynomial
public import Mathlib.RingTheory.MvPolynomial.Ideal
public import TauCeti.AlgebraicGeometry.Morphisms.Smooth.CohenMacaulay
public import TauCeti.RingTheory.CohenMacaulay.Catenary
public import TauCeti.RingTheory.CohenMacaulay.Localization
public import TauCeti.RingTheory.KrullDimension.Module

/-!
# Tests for Cohen–Macaulay schemes

The spectrum of a field and the affine plane over a field are Cohen–Macaulay, being regular. The
spectrum of an Artinian ring, such as the non-reduced and hence non-regular `k[ε] = k[X] ⧸ (X²)`,
is Cohen–Macaulay because its local rings have dimension zero. The affine plane over such a ring
is smooth over it, so it is again Cohen–Macaulay without being regular.

On the plane `Spec k[x, y]`, the coherent module of `k[x, y] ⧸ (x, y)` is Cohen–Macaulay: its
support is the origin, of dimension `0`. The coherent module of `k[x, y] ⧸ (x², xy)` is not: its
support is the line `x = 0`, of dimension `1`, but the origin is an embedded point, so the stalk
there has depth `0`. Finally, the union `Spec k[x, y, z] ⧸ (xz, yz)` of a plane and a line meeting
at the origin is not Cohen–Macaulay: at the origin, the dimension formula
`ht P + ht (Q / P) = ht Q` of a Cohen–Macaulay local ring fails for the line `P`, as `0 + 1 < 2`.
-/

public section

namespace AlgebraicGeometry.Scheme

universe u

/-- *test_field*: the spectrum of a field is Cohen–Macaulay. -/
example (k : Type u) [Field k] : (Spec (CommRingCat.of k)).IsCohenMacaulay :=
  inferInstance

/-- *test_affinePlane*: the affine plane `Spec k[x, y]` over a field is Cohen–Macaulay. -/
example (k : Type u) [Field k] :
    (Spec (CommRingCat.of (MvPolynomial (Fin 2) k))).IsCohenMacaulay :=
  inferInstance

/-- The spectrum of an Artinian ring is Cohen–Macaulay: its local rings have dimension zero. This
includes non-regular schemes such as `Spec k[ε]`. -/
example (R : CommRingCat.{u}) [IsArtinianRing R] : (Spec R).IsCohenMacaulay :=
  (isCohenMacaulay_Spec_iff R).mpr
    TauCeti.Ring.IsCohenMacaulay.of_krullDimLE_zero

/-- The affine plane over an Artinian ring, such as `k[ε]`, is smooth over a Cohen–Macaulay
scheme and hence Cohen–Macaulay. -/
example (R : CommRingCat.{u}) [IsArtinianRing R] :
    (Spec (CommRingCat.of (MvPolynomial (Fin 2) R))).IsCohenMacaulay :=
  have : (Spec R).IsCohenMacaulay :=
    (isCohenMacaulay_Spec_iff R).mpr TauCeti.Ring.IsCohenMacaulay.of_krullDimLE_zero
  have : Smooth (Spec.map (CommRingCat.ofHom (algebraMap R (MvPolynomial (Fin 2) R)))) :=
    HasRingHomProperty.Spec_iff.mpr (RingHom.smooth_algebraMap.mpr inferInstance)
  .of_smooth (Spec.map (CommRingCat.ofHom (algebraMap R (MvPolynomial (Fin 2) R))))

section Plane

open MvPolynomial

variable {k : Type u} [Field k]

/-- The ideal `(x, y)` of the origin in `k[x, y]` is the kernel of the constant coefficient. -/
private theorem span_X_eq_ker_constantCoeff :
    Ideal.span {(X 0 : MvPolynomial (Fin 2) k), X 1} = RingHom.ker (constantCoeff (R := k)) := by
  refine le_antisymm (Ideal.span_le.2 ?_) fun f hf ↦ ?_
  · rw [Set.insert_subset_iff, Set.singleton_subset_iff]
    simp
  have hX : ({X 0, X 1} : Set (MvPolynomial (Fin 2) k)) = X '' Set.univ := by
    ext p
    simp [Fin.exists_fin_two, eq_comm]
  -- Every monomial of `f` is nonconstant, since `f` has no constant term.
  rw [hX, mem_ideal_span_X_image]
  intro m hm
  have hm0 : m ≠ 0 := by
    rintro rfl
    exact (mem_support_iff.1 hm) (by rwa [← constantCoeff_eq, ← RingHom.mem_ker])
  obtain ⟨i, hi⟩ := Finsupp.ne_iff.1 hm0
  exact ⟨i, Set.mem_univ i, hi⟩

/-- The origin `(x, y)` is a maximal ideal of `k[x, y]`. -/
local instance isMaximal_span_X :
    (Ideal.span {(X 0 : MvPolynomial (Fin 2) k), X 1}).IsMaximal := by
  rw [span_X_eq_ker_constantCoeff]
  exact RingHom.ker_isMaximal_of_surjective _ fun a ↦ ⟨C a, constantCoeff_C ..⟩

/-- *Scheme.Modules.IsCohenMacaulay.test_point_on_plane*, first half: on the plane
`Spec k[x, y]`, the coherent module of `k[x, y] ⧸ (x, y)` is Cohen–Macaulay, of depth `0` with
support a point. -/
example : (tilde (ModuleCat.of (CommRingCat.of (MvPolynomial (Fin 2) k))
    (MvPolynomial (Fin 2) k ⧸
      Ideal.span {(X 0 : MvPolynomial (Fin 2) k), X 1}))).IsCohenMacaulay := by
  rw [Modules.isCohenMacaulay_tilde_iff]
  intro p _
  by_cases hp : Ideal.span {(X 0 : MvPolynomial (Fin 2) k), X 1} ≤ p
  · -- The support is the origin alone.
    apply Module.isCohenMacaulay_localizedModule_of_mem_minimalPrimes
    rw [Ideal.annihilator_quotient,
      ← Ideal.IsMaximal.eq_of_le inferInstance Ideal.IsPrime.ne_top' hp,
      Ideal.minimalPrimes_eq_subsingleton_self]
    rfl
  · -- Away from the origin the stalk vanishes.
    have : Subsingleton (LocalizedModule p.primeCompl
        (MvPolynomial (Fin 2) k ⧸ Ideal.span {(X 0 : MvPolynomial (Fin 2) k), X 1})) := by
      rw [← not_nontrivial_iff_subsingleton, ← Module.mem_support_iff (p := ⟨p, ‹_›⟩),
        Module.mem_support_iff_of_finite, Ideal.annihilator_quotient]
      exact hp
    exact Module.isCohenMacaulay_of_subsingleton

/-- *Scheme.Modules.IsCohenMacaulay.test_point_on_plane*, second half: on the plane
`Spec k[x, y]`, the coherent module of `k[x, y] ⧸ (x², xy)` is not Cohen–Macaulay. Its stalk at
the origin has depth `0`, since the origin is the annihilator of the class of `x`, but its support
contains the line `x = 0`. -/
example : ¬ (tilde (ModuleCat.of (CommRingCat.of (MvPolynomial (Fin 2) k))
    (MvPolynomial (Fin 2) k ⧸
      Ideal.span {(X 0 ^ 2 : MvPolynomial (Fin 2) k), X 0 * X 1}))).IsCohenMacaulay := by
  rw [Modules.isCohenMacaulay_tilde_iff]
  intro h
  set m := Ideal.span {(X 0 : MvPolynomial (Fin 2) k), X 1}
  set I := Ideal.span {(X 0 ^ 2 : MvPolynomial (Fin 2) k), X 0 * X 1}
  have : m.IsMaximal := isMaximal_span_X
  -- The origin is an associated prime: it is the annihilator of the class of `x`.
  have hass : m ∈ associatedPrimes (MvPolynomial (Fin 2) k) (MvPolynomial (Fin 2) k ⧸ I) := by
    refine isAssociatedPrime_iff.2 ⟨inferInstance, Ideal.Quotient.mk I (X 0), ?_⟩
    ext f
    rw [Submodule.mem_colon_singleton, Submodule.mem_bot, ← Ideal.Quotient.mk_eq_mk,
      ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, smul_eq_mul]
    refine ⟨fun hf ↦ ?_, fun hf ↦ ?_⟩
    · obtain ⟨a, b, rfl⟩ := Ideal.mem_span_pair.1 hf
      exact Ideal.mem_span_pair.2 ⟨a, b, by ring⟩
    · obtain ⟨a, b, hab⟩ := Ideal.mem_span_pair.1 hf
      refine Ideal.mem_span_pair.2 ⟨a, b, ?_⟩
      have : X 0 * (a * X 0 + b * X 1 - f) = 0 := by linear_combination hab
      rw [mul_eq_zero, sub_eq_zero] at this
      exact this.resolve_left (X_ne_zero 0)
  -- The origin is not minimal in the support: the line `x = 0` lies in between.
  have hmin : m ∉ I.minimalPrimes := fun hm ↦ by
    have hq : (Ideal.span {(X 0 : MvPolynomial (Fin 2) k)}).IsPrime := by
      simpa using span_X_image_isPrime (R := k) ({0} : Set (Fin 2))
    have hIq : I ≤ Ideal.span {X 0} := by
      rw [Ideal.span_le, Set.insert_subset_iff, Set.singleton_subset_iff]
      exact ⟨Ideal.mem_span_singleton.2 (dvd_pow_self _ two_ne_zero),
        Ideal.mem_span_singleton.2 (dvd_mul_right _ _)⟩
    have hX1 : (X 1 : MvPolynomial (Fin 2) k) ∈ Ideal.span {X 0} :=
      hm.2 ⟨hq, hIq⟩ (Ideal.span_mono (by simp)) (Ideal.subset_span (by simp))
    rw [← Set.image_singleton, mem_ideal_span_X_image] at hX1
    obtain ⟨i, hi, hne⟩ := hX1 (Finsupp.single 1 1) (by simp [support_X])
    simp_all
  have hIm : I ≤ m := Ideal.span_le.2 <| by
    rw [Set.insert_subset_iff, Set.singleton_subset_iff]
    exact ⟨Ideal.pow_mem_of_mem _ (Ideal.subset_span (by simp)) 2 two_pos,
      Ideal.mul_mem_right _ _ (Ideal.subset_span (by simp))⟩
  -- So the stalk at the origin has depth `0` but a support of positive dimension.
  have hdepth := TauCeti.depth_localizedModule_eq_zero_iff.2 hass
  have hsupp := (Module.supportDim_localizedModule_nonpos_iff
    (M := MvPolynomial (Fin 2) k ⧸ I) (p := m) (by rwa [Ideal.annihilator_quotient])).not.2
    (by rwa [Ideal.annihilator_quotient])
  rcases (Module.isCohenMacaulay_iff _ _).1 (h m) with hs | hcm
  · exact absurd (hdepth.symm.trans (IsLocalRing.depth_eq_top_of_subsingleton _)) (by decide)
  · rw [hdepth] at hcm
    exact hsupp (hcm ▸ le_rfl)

end Plane

section Cone

open MvPolynomial

variable (k : Type u) [Field k]

/-- The ring `k[x, y, z] ⧸ (xz, yz)` of a plane and a line meeting at a point. -/
private abbrev Cone :=
  MvPolynomial (Fin 3) k ⧸ Ideal.span {(X 0 * X 2 : MvPolynomial (Fin 3) k), X 1 * X 2}

/-- The coordinate functions `x`, `y`, `z` on `k[x, y, z] ⧸ (xz, yz)`. -/
private noncomputable abbrev coneX (i : Fin 3) : Cone k := Ideal.Quotient.mk _ (X i)

variable {k}

/-- Evaluation of `k[x, y, z] ⧸ (xz, yz)` at a point `v` with `v₀ v₂ = v₁ v₂ = 0`. -/
private noncomputable def coneEval {S : Type u} [CommRing S] [Algebra k S] (v : Fin 3 → S)
    (h₀ : v 0 * v 2 = 0) (h₁ : v 1 * v 2 = 0) : Cone k →ₐ[k] S :=
  Ideal.Quotient.liftₐ _ (aeval v) fun a ha ↦ by
    have : Ideal.span {(X 0 * X 2 : MvPolynomial (Fin 3) k), X 1 * X 2} ≤
        RingHom.ker (aeval (R := k) v) := by
      rw [Ideal.span_le, Set.insert_subset_iff, Set.singleton_subset_iff]
      simp [h₀, h₁]
    exact this ha

/-- The evaluation at `v` sends the coordinate functions to the coordinates of `v`. -/
private theorem coneEval_coneX {S : Type u} [CommRing S] [Algebra k S] (v : Fin 3 → S)
    (h₀ : v 0 * v 2 = 0) (h₁ : v 1 * v 2 = 0) (i : Fin 3) :
    coneEval v h₀ h₁ (coneX k i) = v i :=
  aeval_X v i

/-- Two `k`-algebra maps out of `k[x, y, z] ⧸ (xz, yz)` agree when they agree on `x`, `y`, `z`. -/
private theorem cone_algHom_ext {S : Type u} [Semiring S] [Algebra k S] {f g : Cone k →ₐ[k] S}
    (h : ∀ i, f (coneX k i) = g (coneX k i)) : f = g :=
  Ideal.Quotient.algHom_ext _ (MvPolynomial.algHom_ext h)

/-- *test_cone*: the union `Spec k[x, y, z] ⧸ (xz, yz)` of a plane and a line meeting at the
origin is not Cohen–Macaulay. In the Cohen–Macaulay local ring at the origin `Q`, the dimension
formula would give `ht P + ht (Q / P) = ht Q` for the line `P = (x, y)`; but `P` is a minimal
prime, `Q / P` is the origin of the line `k[z]`, of height at most `1`, and the chain
`(z) ⊊ (y, z) ⊊ Q` through the plane gives `ht Q ≥ 2`. -/
example : ¬ (Spec (CommRingCat.of (Cone k))).IsCohenMacaulay := by
  rw [isCohenMacaulay_Spec_iff]
  intro hCM
  -- Evaluations at the origin `Q`, along the line `P`, along the plane `P₁ = (z)` and along the
  -- line `P₂ = (y, z)` in the plane.
  let ε := coneEval (k := k) (S := k) (fun _ ↦ 0) (by simp) (by simp)
  let φ := coneEval (k := k) (S := Polynomial k) ![0, 0, Polynomial.X] (by simp) (by simp)
  let ψ₁ := coneEval (k := k) (S := MvPolynomial (Fin 2) k) ![X 0, X 1, 0] (by simp) (by simp)
  let ψ₂ := coneEval (k := k) (S := Polynomial k) ![Polynomial.X, 0, 0] (by simp) (by simp)
  let Q := RingHom.ker ε
  let P := RingHom.ker φ
  let P₁ := RingHom.ker ψ₁
  let P₂ := RingHom.ker ψ₂
  have : Q.IsPrime := RingHom.ker_isPrime ε
  have : P.IsPrime := RingHom.ker_isPrime φ
  have : P₁.IsPrime := RingHom.ker_isPrime ψ₁
  have : P₂.IsPrime := RingHom.ker_isPrime ψ₂
  have hεφ : ε = (Polynomial.aeval 0).comp φ :=
    cone_algHom_ext fun i ↦ by fin_cases i <;> simp [ε, φ, coneEval_coneX]
  have hεψ : ε = (Polynomial.aeval 0).comp ψ₂ :=
    cone_algHom_ext fun i ↦ by fin_cases i <;> simp [ε, ψ₂, coneEval_coneX]
  have hψ : ψ₂ = (aeval ![Polynomial.X, 0]).comp ψ₁ :=
    cone_algHom_ext fun i ↦ by fin_cases i <;> simp [ψ₁, ψ₂, coneEval_coneX]
  have hPQ : P ≤ Q := fun a ha ↦ by
    rw [RingHom.mem_ker] at ha ⊢
    rw [hεφ, AlgHom.comp_apply, ha, map_zero]
  -- The chain `P₁ < P₂ < Q` gives `ht Q ≥ 2`.
  have h₁₂ : P₁ < P₂ := IsConcreteLE.lt_iff_le_and_exists.2
    ⟨fun a ha ↦ by
      rw [RingHom.mem_ker] at ha ⊢
      rw [hψ, AlgHom.comp_apply, ha, map_zero],
      coneX k 1, by simp [P₂, ψ₂, coneEval_coneX], by simp [P₁, ψ₁, coneEval_coneX, X_ne_zero]⟩
  have h₂Q : P₂ < Q := IsConcreteLE.lt_iff_le_and_exists.2
    ⟨fun a ha ↦ by
      rw [RingHom.mem_ker] at ha ⊢
      rw [hεψ, AlgHom.comp_apply, ha, map_zero],
      coneX k 0, by simp [Q, ε, coneEval_coneX],
      by simp [P₂, ψ₂, coneEval_coneX, Polynomial.X_ne_zero]⟩
  have hQ : 2 ≤ Q.height := by
    have h1 := Ideal.height_add_one_le_of_lt_of_isPrime h₁₂
    have h2 := Ideal.height_add_one_le_of_lt_of_isPrime h₂Q
    calc (2 : ℕ∞) ≤ P₁.height + 1 + 1 := by rw [add_assoc, one_add_one_eq_two]; exact le_add_self
      _ ≤ P₂.height + 1 := by gcongr
      _ ≤ Q.height := h2
  -- The line `P = (x, y)` is a minimal prime: it kills `z ∉ P`.
  have hzP : coneX k 2 ∉ P := by simp [P, φ, coneEval_coneX, Polynomial.X_ne_zero]
  have hxz : coneX k 0 * coneX k 2 = 0 := by
    rw [← map_mul, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.subset_span (by simp)
  have hyz : coneX k 1 * coneX k 2 = 0 := by
    rw [← map_mul, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.subset_span (by simp)
  have hPz (a : Cone k) (ha : a ∈ P) : a * coneX k 2 = 0 := by
    -- Modulo `K = (x, y)` the ring is `k[z]`, so `a ∈ P` lies in `K`.
    let K := Ideal.span {coneX k 0, coneX k 1}
    let g : Polynomial k →ₐ[k] Cone k ⧸ K := Polynomial.aeval (Ideal.Quotient.mk K (coneX k 2))
    have hg : Ideal.Quotient.mkₐ k K = g.comp φ := by
      refine cone_algHom_ext (f := Ideal.Quotient.mkₐ k K) (g := g.comp φ) fun i ↦ ?_
      rw [AlgHom.comp_apply, coneEval_coneX, Ideal.Quotient.mkₐ_eq_mk]
      fin_cases i
      · simpa [Ideal.Quotient.eq_zero_iff_mem, K] using Ideal.subset_span (by simp)
      · simpa [Ideal.Quotient.eq_zero_iff_mem, K] using Ideal.subset_span (by simp)
      · simp [g]
    have haK : a ∈ K := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, ← Ideal.Quotient.mkₐ_eq_mk k, hg, AlgHom.comp_apply,
        RingHom.mem_ker.1 ha, map_zero]
    obtain ⟨b, c, rfl⟩ := Ideal.mem_span_pair.1 haK
    rw [add_mul, mul_assoc, mul_assoc, hxz, hyz, mul_zero, mul_zero, add_zero]
  have hP : P.height = 0 := Ideal.height_eq_zero_iff.2
    ⟨⟨inferInstance, bot_le⟩, fun q ⟨hq, _⟩ hqP a ha ↦
      (hq.mem_or_mem (hPz a ha ▸ q.zero_mem)).resolve_right fun hz ↦ hzP (hqP hz)⟩
  -- `ht (Q / P) ≤ dim k[z] = 1`.
  have hφ : Function.Surjective φ := fun f ↦ ⟨Polynomial.aeval (coneX k 2) f, by
    rw [← Polynomial.aeval_algHom_apply, coneEval_coneX]
    simp⟩
  have hQP : (Q.map (Ideal.Quotient.mk P)).height ≤ 1 := by
    have : (Q.map (Ideal.Quotient.mk P)).IsPrime :=
      Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by rwa [Ideal.mk_ker])
    have h := Ideal.height_le_ringKrullDim_of_ne_top (I := Q.map (Ideal.Quotient.mk P))
      this.ne_top
    rw [ringKrullDim_eq_of_ringEquiv (Ideal.quotientKerAlgEquivOfSurjective hφ).toRingEquiv,
      Polynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field, zero_add] at h
    exact_mod_cast h
  -- But `ht P + ht (Q / P) = ht Q` in the Cohen–Macaulay local ring at `Q`.
  have hsum := (hCM.isCohenMacaulay_localization Q).height_add_height_map_quotientMk hPQ
  rw [hP, zero_add] at hsum
  exact absurd (hQ.trans (hsum ▸ hQP)) (by decide)

end Cone

end AlgebraicGeometry.Scheme
