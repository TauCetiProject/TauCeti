/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Kaehler.DeRham.Quotient
public import TauCeti.RingTheory.Kaehler.DividedPowers
import TauCeti.Algebra.Subalgebra.Centralizer
import TauCeti.LinearAlgebra.ExteriorPower.Basic

/-!
# The divided power de Rham algebra

The divided power de Rham algebra is the exterior algebra of the divided power Kähler
differentials. The ordinary exterior derivative descends to it because the differential of
each divided power relation maps to zero by alternation, also in characteristic two.
The quotient is a morphism of DG algebras and carries the universal property of the
ordinary de Rham algebra to maps satisfying the divided power chain rule.

## References

* [Stacks Project, Remark 60.6.7](https://stacks.math.columbia.edu/tag/07HZ).
-/

public section

noncomputable section

open CliffordAlgebra KaehlerDifferential

namespace TauCeti.PDDeRham

variable {R B : Type*} [CommRing R] [CommRing B] [Algebra R B] {I : Ideal B}
  {δ : DividedPowers I}

/-- The exterior algebra of the divided power Kähler differentials. -/
abbrev Forms (R : Type*) [CommRing R] [Algebra R B] (δ : DividedPowers I) :=
  ExteriorAlgebra B (PDKaehlerDifferential R δ)

variable (δ)

variable (R) in
/-- The quotient from the ordinary de Rham algebra to the divided power de Rham algebra. -/
def ofKaehler : ExteriorAlgebra B Ω[B⁄R] →ₐ[B] Forms R δ :=
  ExteriorAlgebra.map (PDKaehlerDifferential.mkQ R δ)

/-- On one-forms the comparison is the quotient by the divided power relations. -/
@[simp]
theorem ofKaehler_ι (ω : Ω[B⁄R]) :
    ofKaehler R δ (ExteriorAlgebra.ι B ω) =
      ExteriorAlgebra.ι B (PDKaehlerDifferential.mkQ R δ ω) :=
  ExteriorAlgebra.map_apply_ι _ _

/-- The comparison from ordinary forms is surjective. -/
theorem ofKaehler_surjective : Function.Surjective (ofKaehler R δ) :=
  ExteriorAlgebra.map_surjective_iff.mpr (Submodule.mkQ_surjective _)

private theorem preDerivOne_relation (n : ℕ) {x : B} (hx : x ∈ I) :
    KaehlerDeRham.preExtDerivOne (PDKaehlerDifferential.mkQ R δ)
      (D R B (δ.dpow (n + 1) x) - δ.dpow n x • D R B x) = 0 := by
  have hd (b : B) : KaehlerDeRham.preExtDerivOne (PDKaehlerDifferential.mkQ R δ) (D R B b) = 0 := by
    rw [KaehlerDeRham.preExtDerivOne_apply, KaehlerDeRham.extDeriv_ι_D, map_zero]
  simp only [map_sub, KaehlerDeRham.preExtDerivOne_smul, hd, smul_zero, add_zero,
    Submodule.mkQ_apply, PDKaehlerDifferential.mk_D, zero_sub, neg_eq_zero]
  cases n with
  | zero => simp [δ.dpow_zero hx]
  | succ n =>
    rw [PDKaehlerDifferential.d_dpow_succ R δ n hx, map_smul, smul_mul_assoc,
      ExteriorAlgebra.ι_sq_zero, smul_zero]

private theorem preDerivOne_eq_zero {ω : Ω[B⁄R]} (hω : PDKaehlerDifferential.mkQ R δ ω = 0) :
    KaehlerDeRham.preExtDerivOne (PDKaehlerDifferential.mkQ R δ) ω = 0 := by
  let q := PDKaehlerDifferential.mkQ R δ
  let L := (LinearMap.ker (KaehlerDeRham.preExtDerivOneKer q)).map (LinearMap.ker q).subtype
  have hq : LinearMap.ker q = PDKaehlerDifferential.relations R δ :=
    Submodule.ker_mkQ (PDKaehlerDifferential.relations R δ)
  have hL : PDKaehlerDifferential.relations R δ ≤ L :=
    (PDKaehlerDifferential.relations_le_iff R δ).mpr fun n x hx ↦ by
      have hrel : D R B (δ.dpow (n + 1) x) - δ.dpow n x • D R B x ∈ LinearMap.ker q := by
        rw [hq]
        exact (PDKaehlerDifferential.relations_le_iff R δ).mp le_rfl n x hx
      refine ⟨⟨_, hrel⟩, LinearMap.mem_ker.mpr ?_, rfl⟩
      rw [KaehlerDeRham.preExtDerivOneKer_apply]
      exact preDerivOne_relation δ n hx
  have hω' : ω ∈ PDKaehlerDifferential.relations R δ := by
    rw [← hq]
    exact LinearMap.mem_ker.mpr hω
  obtain ⟨η, hη, rfl⟩ := hL hω'
  exact (KaehlerDeRham.preExtDerivOneKer_apply q η).symm.trans (LinearMap.mem_ker.mp hη)

variable (R) in
/-- The exterior derivative on divided power forms, extending the universal PD derivation
and satisfying the graded Leibniz rule. -/
def extDeriv : Forms R δ →ₗ[R] Forms R δ :=
  KaehlerDeRham.extDerivDescend (PDKaehlerDifferential.mkQ R δ) (Submodule.mkQ_surjective _)
    (fun _ hω ↦ preDerivOne_eq_zero δ hω)

variable {δ}

/-- On scalars the exterior derivative is the universal divided power derivation. -/
@[simp]
theorem extDeriv_algebraMap (b : B) :
    extDeriv R δ (algebraMap B (Forms R δ) b) =
      ExteriorAlgebra.ι B (PDKaehlerDifferential.d R δ b) := by
  rw [extDeriv, KaehlerDeRham.extDerivDescend_algebraMap, Submodule.mkQ_apply,
    PDKaehlerDifferential.mk_D]

/-- Exact one-forms are closed. -/
@[simp]
theorem extDeriv_ι_d (b : B) :
    extDeriv R δ (ExteriorAlgebra.ι B (PDKaehlerDifferential.d R δ b)) = 0 := by
  rw [← PDKaehlerDifferential.mk_D, ← Submodule.mkQ_apply, extDeriv]
  exact KaehlerDeRham.extDerivDescend_ι_map_D _ _ _ b

/-- The exterior derivative satisfies the graded Leibniz rule expressed by the grade involution. -/
theorem extDeriv_mul (x y : Forms R δ) :
    extDeriv R δ (x * y) = extDeriv R δ x * y +
      involute (Q := (0 : QuadraticForm B (PDKaehlerDifferential R δ))) x * extDeriv R δ y :=
  KaehlerDeRham.extDerivDescend_mul _ _ _ x y

/-- The quotient by the divided power relations commutes with exterior differentiation. -/
theorem extDeriv_ofKaehler (x : ExteriorAlgebra B Ω[B⁄R]) :
    extDeriv R δ (ofKaehler R δ x) = ofKaehler R δ (KaehlerDeRham.extDeriv R B x) :=
  KaehlerDeRham.extDerivDescend_map _ _ _ x

/-- The exterior derivative on divided power forms squares to zero. -/
@[simp]
theorem extDeriv_extDeriv (x : Forms R δ) : extDeriv R δ (extDeriv R δ x) = 0 :=
  KaehlerDeRham.extDerivDescend_sq _ _ _ x

variable (R δ)

/-- The cohomological grading of the divided power de Rham algebra by exterior degree. -/
def grading (n : ℤ) : Submodule R (Forms R δ) :=
  (TauCeti.ExteriorAlgebra.integerGrading B (PDKaehlerDifferential R δ) n).restrictScalars R

instance gradedAlgebra : GradedAlgebra (grading R δ) :=
  inferInstanceAs <| GradedAlgebra fun n ↦
    (TauCeti.ExteriorAlgebra.integerGrading B (PDKaehlerDifferential R δ) n).restrictScalars R

/-- Membership in the cohomological grading is membership in the exterior grading. -/
theorem mem_grading_iff {n : ℤ} {x : Forms R δ} :
    x ∈ grading R δ n ↔
      x ∈ TauCeti.ExteriorAlgebra.integerGrading B (PDKaehlerDifferential R δ) n :=
  (Iff.rfl)

/-- Scalars from the divided power ring have degree zero. -/
theorem algebraMap_mem_grading_zero (b : B) :
    algebraMap B (Forms R δ) b ∈ grading R δ 0 := by
  rw [mem_grading_iff, ← Nat.cast_zero, TauCeti.ExteriorAlgebra.integerGrading_natCast,
    _root_.ExteriorAlgebra.exteriorPower, pow_zero]
  exact Submodule.algebraMap_mem b

/-- The exterior derivative raises exterior degree by one. -/
theorem extDeriv_mem_grading {n : ℤ} {x : Forms R δ}
    (hx : x ∈ grading R δ n) : extDeriv R δ x ∈ grading R δ (n + 1) :=
  KaehlerDeRham.extDerivDescend_mem_integerGrading _ _ _ hx

/-- Divided power forms with the exterior differential are a differential graded algebra. -/
theorem isDGAlgebra : IsDGAlgebra (grading R δ) (extDeriv R δ) where
  map_mem := extDeriv_mem_grading R δ
  sq_zero := extDeriv_extDeriv
  leibniz hx y := by
    rw [extDeriv_mul, TauCeti.ExteriorAlgebra.involute_of_mem_integerGrading hx, smul_mul_assoc]

/-- The quotient from ordinary to divided power forms as a morphism of DG algebras. -/
def ofKaehlerDGAlgHom : DGAlgHom (KaehlerDeRham.isDGAlgebra R B) (isDGAlgebra R δ) where
  toGradedAlgHom :=
    { toAlgHom := (ofKaehler R δ).restrictScalars R
      map_mem := fun hx ↦ (mem_grading_iff R δ).mpr <|
        TauCeti.ExteriorAlgebra.map_mem_integerGrading (PDKaehlerDifferential.mkQ R δ)
          (KaehlerDeRham.mem_grading_iff.mp hx) }
  map_d' := extDeriv_ofKaehler

/-- The DG quotient acts by the exterior algebra map on forms. -/
@[simp]
theorem ofKaehlerDGAlgHom_apply (x : ExteriorAlgebra B Ω[B⁄R]) :
    ofKaehlerDGAlgHom R δ x = ofKaehler R δ x :=
  (rfl)

section UniversalProperty

variable {P : Type*} [Ring P] [Algebra R P] {ℬ : ℤ → Submodule R P} [GradedAlgebra ℬ]
  {dP : P →ₗ[R] P}

private def factorAlgHom (F : ExteriorAlgebra B Ω[B⁄R] →ₐ[R] P)
    (hF : ∀ (n : ℕ) (x : B), x ∈ I →
      F (ExteriorAlgebra.ι B (D R B (δ.dpow (n + 1) x) - δ.dpow n x • D R B x)) = 0) :
    { G : Forms R δ →ₐ[R] P // ∀ ω, G (ofKaehler R δ ω) = F ω } := by
  let f := F.comp (IsScalarTower.toAlgHom R B (ExteriorAlgebra B Ω[B⁄R]))
  let S := Subalgebra.centralizer R (Set.range f)
  letI : Algebra B S := f.centralizerRangeAlgebra
  letI : IsScalarTower R B S := f.centralizerRangeIsScalarTower
  have hS (b : B) : (algebraMap B S b : P) = f b := f.coe_algebraMap_centralizerRange b
  have hi (ω : Ω[B⁄R]) : F (ExteriorAlgebra.ι B ω) ∈ S := by
    apply (Subalgebra.mem_centralizer_iff R).mpr
    rintro _ ⟨b, rfl⟩
    simpa only [f, AlgHom.comp_apply, IsScalarTower.toAlgHom_apply, map_mul] using
      congrArg F (Algebra.commutes b (ExteriorAlgebra.ι B ω))
  let L : Ω[B⁄R] →ₗ[B] S :=
    { toFun := fun ω ↦ ⟨F (ExteriorAlgebra.ι B ω), hi ω⟩
      map_add' := fun x y ↦ Subtype.ext <| by simp
      map_smul' := fun b ω ↦ Subtype.ext <| by
        simp [Algebra.smul_def, hS, f] }
  let L' := (PDKaehlerDifferential.relations R δ).liftQ L <| by
    rw [PDKaehlerDifferential.relations_le_iff]
    intro n x hx
    exact LinearMap.mem_ker.mpr (Subtype.ext (hF n x hx))
  have hsq (ω : PDKaehlerDifferential R δ) : L' ω * L' ω = 0 := by
    obtain ⟨ω, rfl⟩ := Submodule.mkQ_surjective (PDKaehlerDifferential.relations R δ) ω
    have hL : L' (PDKaehlerDifferential.mkQ R δ ω) = L ω := Submodule.liftQ_apply _ L ω
    rw [hL]
    exact Subtype.ext <| (map_mul F _ _).symm.trans (by
      rw [ExteriorAlgebra.ι_sq_zero, map_zero]
      rfl)
  let G := ExteriorAlgebra.lift B ⟨L', hsq⟩
  refine ⟨S.val.comp (G.restrictScalars R), ?_⟩
  intro ω
  induction ω using ExteriorAlgebra.induction with
  | algebraMap b =>
    rw [AlgHom.commutes, AlgHom.comp_apply, AlgHom.coe_restrictScalars', AlgHom.commutes]
    exact hS b
  | ι ω =>
    rw [ofKaehler_ι, AlgHom.comp_apply, AlgHom.coe_restrictScalars',
      ExteriorAlgebra.lift_ι_apply]
    rfl
  | mul x y hx hy => simp only [map_mul, hx, hy]
  | add x y hx hy => simp only [map_add, hx, hy]

private theorem exists_ofKaehler_of_mem_grading {n : ℤ} {x : Forms R δ}
    (hx : x ∈ grading R δ n) :
    ∃ y ∈ KaehlerDeRham.grading R B n, ofKaehler R δ y = x := by
  obtain ⟨y, rfl⟩ := ofKaehler_surjective δ x
  let z := DirectSum.decompose (KaehlerDeRham.grading R B) y n
  refine ⟨z, z.property, ?_⟩
  rw [← ofKaehlerDGAlgHom_apply,
    map_directSumDecompose (KaehlerDeRham.grading R B) (grading R δ),
    ofKaehlerDGAlgHom_apply, DirectSum.decompose_of_mem_same _ hx]

private theorem ordinaryLift_kills_relations (hP : IsDGAlgebra ℬ dP) (f : B →ₐ[R] P)
    (hf₀ : ∀ b : B, f b ∈ ℬ 0)
    (hcomm : ∀ b c : B, f b * dP (f c) = dP (f c) * f b)
    (hsq : ∀ b : B, dP (f b) * dP (f b) = 0)
    (hPD : ∀ (n : ℕ) (x : B), x ∈ I →
      dP (f (δ.dpow (n + 1) x)) = f (δ.dpow n x) * dP (f x))
    (n : ℕ) (x : B) (hx : x ∈ I) :
    KaehlerDeRham.liftDGAlgHom hP f hf₀ hcomm hsq
      (ExteriorAlgebra.ι B (D R B (δ.dpow (n + 1) x) - δ.dpow n x • D R B x)) = 0 := by
  simp only [map_sub, LinearMap.map_smul, KaehlerDeRham.liftDGAlgHom_smul,
    KaehlerDeRham.liftDGAlgHom_ι_D, hPD n x hx, sub_self]

/-- An algebra map to degree zero of a DG algebra extends to divided power forms if its
differential satisfies the divided power chain rule. The differential of each image element
must commute with the degree-zero image and have zero multiplicative square. -/
def liftDGAlgHom (hP : IsDGAlgebra ℬ dP) (f : B →ₐ[R] P)
    (hf₀ : ∀ b : B, f b ∈ ℬ 0)
    (hcomm : ∀ b c : B, f b * dP (f c) = dP (f c) * f b)
    (hsq : ∀ b : B, dP (f b) * dP (f b) = 0)
    (hPD : ∀ (n : ℕ) (x : B), x ∈ I →
      dP (f (δ.dpow (n + 1) x)) = f (δ.dpow n x) * dP (f x)) :
    DGAlgHom (isDGAlgebra R δ) hP := by
  let F := KaehlerDeRham.liftDGAlgHom hP f hf₀ hcomm hsq
  let G := factorAlgHom R δ F.toGradedAlgHom.toAlgHom
    (ordinaryLift_kills_relations R δ hP f hf₀ hcomm hsq hPD)
  refine ⟨⟨G.val, ?_⟩, ?_⟩
  · intro n x hx
    obtain ⟨y, hy, rfl⟩ := exists_ofKaehler_of_mem_grading R δ hx
    exact G.property y ▸ F.toGradedAlgHom.map_mem hy
  · intro x
    obtain ⟨y, rfl⟩ := ofKaehler_surjective δ x
    rw [extDeriv_ofKaehler]
    exact (congrArg dP (G.property y)).trans <|
      (F.map_d y).trans (G.property _).symm

section Lift

variable (hP : IsDGAlgebra ℬ dP) (f : B →ₐ[R] P) (hf₀ : ∀ b : B, f b ∈ ℬ 0)
    (hcomm : ∀ b c : B, f b * dP (f c) = dP (f c) * f b)
    (hsq : ∀ b : B, dP (f b) * dP (f b) = 0)
    (hPD : ∀ (n : ℕ) (x : B), x ∈ I →
      dP (f (δ.dpow (n + 1) x)) = f (δ.dpow n x) * dP (f x))

/-- The lift out of divided power forms factors the ordinary de Rham lift. -/
theorem liftDGAlgHom_ofKaehler (ω : ExteriorAlgebra B Ω[B⁄R]) :
    liftDGAlgHom R δ hP f hf₀ hcomm hsq hPD (ofKaehler R δ ω) =
      KaehlerDeRham.liftDGAlgHom hP f hf₀ hcomm hsq ω :=
  (factorAlgHom R δ _ (ordinaryLift_kills_relations R δ hP f hf₀ hcomm hsq hPD)).property ω

/-- On scalars the divided power de Rham lift agrees with the given algebra map. -/
@[simp]
theorem liftDGAlgHom_algebraMap (b : B) :
    liftDGAlgHom R δ hP f hf₀ hcomm hsq hPD (algebraMap B (Forms R δ) b) = f b := by
  rw [← AlgHom.commutes (ofKaehler R δ), liftDGAlgHom_ofKaehler,
    KaehlerDeRham.liftDGAlgHom_algebraMap]

/-- The divided power de Rham lift sends `db` to the differential of `f b`. -/
@[simp]
theorem liftDGAlgHom_ι_d (b : B) :
    liftDGAlgHom R δ hP f hf₀ hcomm hsq hPD (ExteriorAlgebra.ι B (PDKaehlerDifferential.d R δ b)) =
      dP (f b) := by
  rw [← extDeriv_algebraMap, ← DGAlgHom.map_d, liftDGAlgHom_algebraMap]

end Lift

/-- Two DG algebra maps from the divided power forms agree if they agree on the base algebra. -/
@[ext]
theorem dgAlgHom_ext {hP : IsDGAlgebra ℬ dP} {F G : DGAlgHom (isDGAlgebra R δ) hP}
    (h : ∀ b : B, F (algebraMap B (Forms R δ) b) = G (algebraMap B (Forms R δ) b)) :
    F = G := by
  have he : F.comp (ofKaehlerDGAlgHom R δ) = G.comp (ofKaehlerDGAlgHom R δ) :=
    KaehlerDeRham.dgAlgHom_ext fun b ↦ by
      simpa only [DGAlgHom.comp_apply, ofKaehlerDGAlgHom_apply, AlgHom.commutes] using h b
  apply DGAlgHom.ext
  intro ω
  obtain ⟨ω, rfl⟩ := ofKaehler_surjective δ ω
  simpa only [DGAlgHom.comp_apply, ofKaehlerDGAlgHom_apply] using DFunLike.congr_fun he ω

end UniversalProperty

section Map

variable {δ} {C E : Type*} [CommRing C] [CommRing E] [Algebra R C] [Algebra R E]
  {J : Ideal C} {K : Ideal E} {ε : DividedPowers J} {ζ : DividedPowers K}
  {f : B →ₐ[R] C} {g : C →ₐ[R] E}

/-- A divided power algebra map induces a morphism of divided power de Rham DG algebras. -/
def map (hf : δ.IsDPMorphism ε f.toRingHom) :
    DGAlgHom (isDGAlgebra R δ) (isDGAlgebra R ε) := by
  refine liftDGAlgHom R δ (isDGAlgebra R ε)
    ((IsScalarTower.toAlgHom R C (Forms R ε)).comp f)
    (fun b ↦ algebraMap_mem_grading_zero R ε (f b))
    (fun b _ ↦ Algebra.commutes (f b) _)
    (fun b ↦ by
      simp only [AlgHom.comp_apply, IsScalarTower.toAlgHom_apply, extDeriv_algebraMap]
      exact ExteriorAlgebra.ι_sq_zero _) ?_
  intro n x hx
  simp only [AlgHom.comp_apply, IsScalarTower.toAlgHom_apply, extDeriv_algebraMap]
  have hd (k : ℕ) : f (δ.dpow k x) = ε.dpow k (f x) := hf.map_dpow hx
  have hfx : f x ∈ J := hf.ideal_comp (Ideal.mem_map_of_mem f.toRingHom hx)
  rw [hd, hd, PDKaehlerDifferential.d_dpow_succ R ε n hfx, map_smul, Algebra.smul_def]

/-- The map of divided power de Rham algebras acts by the given map on scalars. -/
@[simp]
theorem map_algebraMap (hf : δ.IsDPMorphism ε f.toRingHom) (b : B) :
    map R hf (algebraMap B (Forms R δ) b) = algebraMap C (Forms R ε) (f b) :=
  liftDGAlgHom_algebraMap _ _ _ _ _ _ _ _ b

/-- On one-forms the map of divided power de Rham algebras acts by the map of PD differentials. -/
@[simp]
theorem map_ι (hf : δ.IsDPMorphism ε f.toRingHom) (ω : PDKaehlerDifferential R δ) :
    map R hf (ExteriorAlgebra.ι B ω) =
      ExteriorAlgebra.ι C (PDKaehlerDifferential.map hf ω) := by
  have hω : ω ∈ Submodule.span B (Set.range (PDKaehlerDifferential.d R δ)) :=
    PDKaehlerDifferential.span_range_d R δ ▸ Submodule.mem_top
  induction hω using Submodule.span_induction with
  | mem _ hx =>
    obtain ⟨b, rfl⟩ := hx
    rw [← extDeriv_algebraMap, ← DGAlgHom.map_d, map_algebraMap, extDeriv_algebraMap,
      PDKaehlerDifferential.map_d hf]
  | zero => simp only [map_zero]
  | add x y _ _ hx hy => simp only [map_add, hx, hy]
  | smul b x _ hx =>
    rw [LinearMap.map_smul, Algebra.smul_def, map_mul, map_algebraMap, hx, ← Algebra.smul_def,
      LinearMap.map_smulₛₗ, LinearMap.map_smul]
    rfl

/-- Identity algebra maps act identically on divided power de Rham algebras. -/
@[simp]
theorem map_id (h : δ.IsDPMorphism δ (AlgHom.id R B).toRingHom) :
    map R h = DGAlgHom.id (isDGAlgebra R δ) :=
  dgAlgHom_ext R δ fun b ↦ (map_algebraMap R h b).trans (DGAlgHom.id_apply _ _).symm

/-- The map of divided power de Rham algebras respects composition. -/
theorem map_comp (hg : ε.IsDPMorphism ζ g.toRingHom) (hf : δ.IsDPMorphism ε f.toRingHom) :
    map R (f := g.comp f) (hg.comp ζ hf) = (map R hg).comp (map R hf) := by
  apply dgAlgHom_ext R δ
  intro b
  refine (map_algebraMap R (f := g.comp f) _ b).trans ?_
  rw [AlgHom.comp_apply, DGAlgHom.comp_apply, map_algebraMap R hf, map_algebraMap R hg]

end Map

end TauCeti.PDDeRham
